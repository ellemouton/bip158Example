package main

import (
	"bytes"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"sort"

	"github.com/aead/siphash"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/btcsuite/btcd/wire"
	"github.com/kkdai/bstream"
	"github.com/toorop/go-bitcoind"
)

const (
	M = 784931
	P = 19
)

func main() {
	bc, err := bitcoind.New("localhost", 18443, "rpcuser", "rpcpassword", false)
	if err != nil {
		log.Fatalln(err)
	}

	blockHash, err := bc.GetBlockHash(2101914)
	if err != nil {
		log.Fatalln(err)
	}

	block, err := bc.GetBlock(blockHash)
	if err != nil {
		log.Fatalln(err)
	}

	filter, N, err := constructFilter(bc, block)
	if err != nil {
		log.Fatalln(err)
	}

	// Prepend the CompactSize N value to the filter.
	var buffer bytes.Buffer
	buffer.Grow(wire.VarIntSerializeSize(uint64(N)) + len(filter))

	err = wire.WriteVarInt(&buffer, 0, uint64(N))
	if err != nil {
		log.Fatalln(err)
	}

	_, err = buffer.Write(filter)
	if err != nil {
		log.Fatalln(err)
	}

	fmt.Println(hex.EncodeToString(buffer.Bytes()))

	err = decode(filter)
	if err != nil {
		log.Fatalln(err)
	}
}

func constructFilter(bc *bitcoind.Bitcoind, block bitcoind.Block) ([]byte, int, error) {
	// The list of objects we want to include in our filter. These will be
	// every scriptPubKey being spent as well as each output's scriptPubKey.
	// We use a map so that we can dedup any duplicate scriptPubKeys.
	objects := make(map[string]struct{})

	for i, txid := range block.Tx {
		rawTx, err := bc.GetRawTransaction(txid, true)
		if err != nil {
			return nil, 0, err
		}

		tx, ok := rawTx.(bitcoind.RawTransaction)
		if !ok {
			return nil, 0, fmt.Errorf("could not convert response " +
				"to bitcoind.RawTransaction")
		}

		// Add the scriptPubKey of each of the transaction's outputs
		// and add those to our list of objects.
		for _, txOut := range tx.Vout {
			skpStr := txOut.ScriptPubKey.Hex

			spk, err := hex.DecodeString(skpStr)
			if err != nil {
				return nil, 0, err
			}

			if len(spk) == 0 {
				continue
			}

			// We don't add the output if it is an OP_RETURN.
			if spk[0] == 0x6a {
				continue
			}

			objects[skpStr] = struct{}{}
		}

		// We don't add the inputs of the coinbase transaction.
		if i == 0 {
			continue
		}

		// For each input, go and fetch the scriptPubKey that it is
		// spending.
		for _, txIn := range tx.Vin {
			rawTx, err := bc.GetRawTransaction(txIn.Txid, true)
			if err != nil {
				return nil, 0, err
			}

			prevTx, ok := rawTx.(bitcoind.RawTransaction)
			if !ok {
				return nil, 0, fmt.Errorf("could not convert " +
					"response to bitcoind.RawTransaction")
			}

			spkStr := prevTx.Vout[txIn.Vout].ScriptPubKey.Hex

			if spkStr == "" {
				continue
			}

			objects[spkStr] = struct{}{}
		}
	}

	// We now have all the objects we want to include in the filter.
	// The next step is getting the objects into numbers distributed
	// uniformly across a space.

	// BIP158 says to use the SipHash function. This is a keyed hash
	// function. The block hash will be used as the key.
	// The BIP also defines 2 other constants: M & P.
	// M, 784931, is defined as the hash range.
	// P, 19, is defined as the collision probability, 2^19.

	N := len(objects)
	F := uint64(N * M)

	// Derive a 16 byte key from the block hash.
	blockHash, err := chainhash.NewHashFromStr(block.Hash)
	if err != nil {
		return nil, 0, err
	}
	var key [16]byte
	copy(key[:], blockHash.CloneBytes())

	numbers := make([]uint64, 0, N)

	// Insert the hash (fast-ranged over a space of N*P) of each data
	// element into a slice.
	for o := range objects {
		b, err := hex.DecodeString(o)
		if err != nil {
			return nil, 0, err
		}

		// Using the given key, max number (F) and object bytes (b),
		// convert the object to a number between 0 and F.
		v := convertToNumber(b, F, key)

		numbers = append(numbers, v)
	}

	// Sort the numbers.
	sort.Slice(numbers, func(i, j int) bool { return numbers[i] < numbers[j] })

	fmt.Println(numbers)

	// Convert the list of numbers to a list of differences.
	differences := make([]uint64, N)
	for i, num := range numbers {
		if i == 0 {
			differences[i] = num
			continue
		}

		differences[i] = num - numbers[i-1]
	}

	// Time for Golomb-Rice Coding!
	filter := bstream.NewBStreamWriter(0)

	// For each number in the differences list, calculate the quotient and
	// remainder after dividing by 2^P.
	for _, d := range differences {
		q := math.Floor(float64(d) / math.Exp2(float64(P)))
		r := d - uint64(math.Exp2(float64(P))*q)

		// Encode the quotient.
		for i := 0; i < int(q); i++ {
			filter.WriteBit(true)
		}
		filter.WriteBit(false)

		filter.WriteBits(r, P)
	}

	return filter.Bytes(), N, nil
}

func convertToNumber(object []byte, F uint64, key [16]byte) uint64 {
	nphi := F >> 32
	nplo := uint64(uint32(F))

	v := siphash.Sum64(object, &key)

	return fastReduction(v, nphi, nplo)
}

// fastReduction calculates a mapping that's more ore less equivalent to: x mod
// N. However, instead of using a mod operation, which using a non-power of two
// will lead to slowness on many processors due to unnecessary division, we
// instead use a "multiply-and-shift" trick which eliminates all divisions,
// described in:
// https://lemire.me/blog/2016/06/27/a-fast-alternative-to-the-modulo-reduction/
//
//  * v * N  >> log_2(N)
//
// In our case, using 64-bit integers, log_2 is 64. As most processors don't
// support 128-bit arithmetic natively, we'll be super portable and unfold the
// operation into several operations with 64-bit arithmetic. As inputs, we the
// number to reduce, and our modulus N divided into its high 32-bits and lower
// 32-bits.
func fastReduction(v, nHi, nLo uint64) uint64 {
	// First, we'll spit the item we need to reduce into its higher and
	// lower bits.
	vhi := v >> 32
	vlo := uint64(uint32(v))

	// Then, we distribute multiplication over each part.
	vnphi := vhi * nHi
	vnpmid := vhi * nLo
	npvmid := nHi * vlo
	vnplo := vlo * nLo

	// We calculate the carry bit.
	carry := (uint64(uint32(vnpmid)) + uint64(uint32(npvmid)) +
		(vnplo >> 32)) >> 32

	// Last, we add the high bits, the middle bits, and the carry.
	v = vnphi + (vnpmid >> 32) + (npvmid >> 32) + carry

	return v
}

func decode(filter []byte) error {
	b := bstream.NewBStreamReader(filter)
	var (
		numbers []uint64
		prevNum uint64
	)

	for {

		// Read a quotient from the stream. Read until we encounter
		// a '0' bit indicating the end of the quotient. The number of
		// '1's we encounter before reaching the '0' defines the
		// quotient.
		var q uint64
		c, err := b.ReadBit()
		if err != nil {
			return err
		}

		for c {
			q++
			c, err = b.ReadBit()
			if errors.Is(err, io.EOF) {
				break
			} else if err != nil {
				return err
			}
		}

		// The following P bits are the remainder encoded as binary.
		r, err := b.ReadBits(P)
		if errors.Is(err, io.EOF) {
			break
		} else if err != nil {
			return err
		}

		n := q*uint64(math.Exp2(float64(P))) + r

		num := n + prevNum
		numbers = append(numbers, num)
		prevNum = num
	}

	fmt.Println(numbers)

	return nil
}
