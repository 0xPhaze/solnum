// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type SM32x32 is uint256;

using SM32x32Lib for SM32x32;

library SM32x32Lib {
    uint256 constant META_DATA_BITS = 24;
    // uint256 constant META_DATA_MAX = 0xffffff; // 24 bits
    // uint256 constant META_DATA_MAX = 0xffffffffffffffff; // 24 bits
    uint256 constant DATA_CHUNK_SIZE = 0x20;

    uint256 constant DATA_BYTES = 0x08;

    uint256 constant WORD = 0x20;
    uint256 constant MAX_04_BITS = 0xf;
    uint256 constant MAX_24_BITS = 0xffffff;
    uint256 constant MAX_64_BITS = 0xffffffffffffffff;

    uint256 constant MAX_32_BITS = 0xffffffff;
    uint256 constant MAX_16_BITS = 0xffff;
    uint256 constant MAX_08_BITS = 0xff;

    /* ------------- header ------------- */

    // struct USM256Header {
    //     uint24 n;
    //     uint24 m;
    // //     uint8 scale; // 1 = 256; 2 = 128
    //     uint64 data;
    //     uint24 startx;
    //     uint24 starty;
    //     uint24 endx;
    //     uint24 endy;
    //     uint8 stridex;
    //     uint8 stridey;
    //     bool T;
    // }

    function USM256Header(uint256 data, uint256 n, uint256 m) internal pure returns (SM32x32 A) {
        assembly {
            A :=
                or(
                    shl(56, data), // data location
                    or(shl(24, m), n) // shape
                )
        }

        require((n | m | (data >> 42)) <= MAX_24_BITS, "SolMat: too large");
    }

    function USM256Header(uint256 data, uint256 n, uint256 m, uint256 scale) internal pure returns (SM32x32 A) {
        assembly {
            A :=
                or(
                    shl(56, data), // data location
                    or(shl(24, m), n) // shape
                )
        }

        require((n | m) <= MAX_24_BITS && scale < 6 && data <= MAX_64_BITS, "SolMat: too large");
    }

    function header(SM32x32 A) internal pure returns (uint256 n, uint256 m, uint256 data, uint256 size) {
        assembly {
            n := and(A, MAX_24_BITS)
            m := and(shr(24, A), MAX_24_BITS)
            size := shr(and(shr(48, A), MAX_04_BITS), WORD) // XXX
            data := and(shr(56, A), MAX_64_BITS)
        }
    }

    function shape(SM32x32 A) internal pure returns (uint256 n, uint256 m) {
        assembly {
            n := and(A, MAX_24_BITS)
            m := and(shr(24, A), MAX_24_BITS)
        }
    }

    function dim0(SM32x32 A) internal pure returns (uint256 n) {
        assembly {
            n := and(A, MAX_24_BITS)
        }
    }

    function dim1(SM32x32 A) internal pure returns (uint256 m) {
        assembly {
            m := and(shr(24, A), MAX_24_BITS)
        }
    }

    function length(SM32x32 A) internal pure returns (uint256 len) {
        assembly {
            let n := and(A, MAX_24_BITS)
            let m := and(shr(24, A), MAX_24_BITS)
            len := mul(n, m)
        }
    }

    function sizeBytes(SM32x32 A) internal pure returns (uint256 size) {
        assembly {
            let n := and(A, MAX_24_BITS)
            let m := and(shr(24, A), MAX_24_BITS)
            let sb := shr(and(shr(48, A), MAX_04_BITS), WORD)
            size := mul(mul(n, m), sb)
        }
    }

    function ref(SM32x32 A) internal pure returns (uint256 data) {
        assembly {
            data := and(shr(56, A), MAX_64_BITS)
        }
    }

    /* ------------- malloc ------------- */

    function malloc(uint256 n, uint256 m, uint256 scale) internal pure returns (uint256 data) {
        assembly {
            data := mload(0x40)
            let size := mul(mul(n, m), shr(scale, WORD))

            // Update free memory pointer.
            // Round up to next multiple of 32 bytes.
            mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))
        }
    }

    function malloc(uint256 n, uint256 m) internal pure returns (uint256 data) {
        assembly {
            data := mload(0x40)
            let size := mul(mul(n, m), WORD)

            // Update free memory pointer.
            // Round up to next multiple of 32 bytes.
            mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))
        }
    }

    function malloc(uint256 size) internal pure returns (uint256 data) {
        assembly {
            data := mload(0x40)

            // Update free memory pointer.
            // Round up to next multiple of 32 bytes.
            mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))
        }
    }

    /* ------------- constructors ------------- */

    function zeros(uint256 n, uint256 m, uint256 scale) internal pure returns (SM32x32 A) {
        // Allocate memory space for matrix.
        uint256 data = malloc(n, m, scale);

        // Generate metadata header.
        A = USM256Header(data, n, m, scale);
    }

    function zeros(uint256 n, uint256 m) internal pure returns (SM32x32 A) {
        // Allocate memory space for matrix.
        uint256 data = malloc(n, m);

        // Generate metadata header.
        A = USM256Header(data, n, m);
    }

    function zeros(uint256 m) internal pure returns (SM32x32 A) {
        // Allocate memory space for matrix.
        uint256 data = malloc(1, m);

        // Generate metadata header.
        A = USM256Header(data, 1, m);
    }

    function ones(uint256 n, uint256 m) internal pure returns (SM32x32 A) {
        A = zeros(n, m);

        (,, uint256 data, uint256 sz) = header(A);

        assembly {
            let ptr := data
            let len := mul(n, m)
            let end := add(ptr, mul(mul(len, m), sz))

            for {} lt(ptr, end) {} {
                mstore(ptr, 1)
                ptr := add(ptr, sz)
            }
        }
    }

    function ones(uint256 m) internal pure returns (SM32x32 A) {
        return ones(1, m);
    }

    function eye(uint256 n, uint256 m) internal pure returns (SM32x32 A) {
        A = zeros(n, m);

        uint256 size = WORD;
        uint256 len = (n < m) ? n : m;
        uint256 ptr = ref(A);

        assembly {
            let end := add(ptr, mul(mul(len, m), size))

            for {} lt(ptr, end) {} {
                mstore(ptr, 1)
                ptr := add(ptr, mul(size, add(1, m)))
            }
        }
    }

    function eye(uint256 n, uint256 m, uint256 scale) internal pure returns (SM32x32 A) {
        A = zeros(n, m, scale);

        uint256 size = WORD >> scale;
        uint256 len = (n < m) ? n : m;
        uint256 ptr = ref(A);

        assembly {
            let end := add(ptr, mul(mul(len, m), size))

            for {} lt(ptr, end) {} {
                mstore(ptr, 1)
                ptr := add(ptr, mul(size, add(1, m)))
            }
        }
    }

    function range(uint256 start, uint256 end) internal pure returns (SM32x32 A) {
        require(start <= end, "SolMat: start <= end");

        uint256 len;

        unchecked {
            len = end - start;
        }

        A = zeros(1, len);

        unchecked {
            for (uint256 i; i < len; ++i) {
                // XXX optimize
                set(A, i, start + i);
            }
        }
    }

    function range(uint256 end) internal pure returns (SM32x32 A) {
        A = zeros(1, end);

        for (uint256 i; i < end; ++i) {
            // XXX optimize
            set(A, i, i);
        }
    }

    function reshape(SM32x32 A, uint256 nNew, uint256 mNew) internal pure returns (SM32x32 out) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

        unchecked {
            require(n * m == nNew * mNew, "SolMat: invalid dimensions");
        }

        uint256 scale;
        if (sz == 16) scale = 1;
        else if (sz == 8) scale = 2;
        else if (sz == 4) scale = 3;
        else if (sz == 2) scale = 4;
        else if (sz == 1) scale = 5;

        out = USM256Header(data, nNew, mNew, scale);
    }

    /* ------------- conversions ------------- */

    /// @dev `data` needs to be contiguous in memory.
    function from(uint8[3][4] memory data) internal pure returns (SM32x32 A) {
        uint256 ptr;

        assembly {
            // Making a big assumption here that `data` uint8[3] entries
            // are laid out contiguously in memory right after the pointers.
            ptr := mload(data)
        }

        A = USM256Header(ptr, 4, 3);
    }

    function from(uint8[3][3] memory data) internal pure returns (SM32x32 A) {
        uint256 ptr;

        assembly {
            ptr := mload(data)
        }

        A = USM256Header(ptr, 3, 3);
    }

    /// @dev todo: compare gas costs to manual copy
    function from(bytes memory dataBytes, uint256 n, uint256 m) internal view returns (SM32x32 A) {
        uint256 size;
        assembly {
            // XXX
            size := mul(DATA_CHUNK_SIZE, mul(n, m))
        }

        uint256 AData = malloc(size);

        assembly {
            // Use address(4) precompile to copy memory data `dataBytes` to `AData`.
            pop(staticcall(gas(), 4, add(0x20, dataBytes), mload(dataBytes), AData, size))
        }

        A = USM256Header(AData, n, m);
    }

    function from_(bytes memory dataBytes, uint256 n, uint256 m) internal pure returns (SM32x32 A) {
        unchecked {
            require(dataBytes.length <= (n * m * DATA_CHUNK_SIZE), "SolMat: too large");
        }

        uint256 AData;

        assembly {
            AData := add(0x20, dataBytes) // Skip length encoding.
        }

        A = USM256Header(AData, n, m);
    }

    function toBytes(SM32x32 A) internal view returns (bytes memory newData) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

        assembly {
            let size := mul(sz, mul(n, m))
            newData := mload(0x40)

            // Update free memory pointer.
            // Round up to next multiple of 32 bytes.
            mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))

            // Use address(4) precompile to copy memory data `dataBytes` to `newData`.
            pop(staticcall(gas(), 4, data, size, add(newData, 0x20), size))
            mstore(newData, size)
        }
    }

    function copy(SM32x32 A) internal view returns (SM32x32 out) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

        uint256 size;

        assembly {
            size := mul(sz, mul(n, m))
        }

        uint256 newData = malloc(size);

        assembly {
            // Use address(4) precompile to copy memory data `dataBytes` to `newData`.
            pop(staticcall(gas(), 4, data, size, newData, size))
        }

        out = USM256Header(newData, n, m);
    }

    // function zeros(uint256 n, uint256 m) internal pure returns (SM32x32 A) {
    //     uint256 data;
    //     uint256 size = DATA_CHUNK_SIZE; // Hardcoding for now.
    //     // note: loading does not take into acc diff sizes

    //     assembly {
    //         A := mload(0x40)
    //         data := add(0x20, A)

    //         // Store meta data.
    //         let len := mul(n, m)
    //         let meta :=
    //             or(
    //                 or(
    //                     shl(mul(3, META_DATA_BITS), size), // data chunk size
    //                     shl(mul(2, META_DATA_BITS), data) // data location
    //                 ),
    //                 or(shl(META_DATA_BITS, m), n) // shape
    //             )

    //         mstore(A, meta)

    //         // Update free memory pointer.
    //         // Round up to next multiple of 32 bytes.
    //         // mstore(0x40, add(data, and(add(mul(size, len), 0x1f), not(0x1f))))
    //         mstore(0x40, add(data, mul(size, len)))
    //     }

    //     require((data | n | m) <= MAX_24_BITS, "SolMat: too large");
    // }

    /* ------------- indexing ------------- */

    function at(SM32x32 A, uint256 index) internal pure returns (uint256 el) {
        (uint256 n, uint256 m, uint256 data,) = header(A);

        unchecked {
            require(index < n * m, "SolMat: out of bounds");
        }

        assembly {
            // let loc := add(data, mul(0x10, index))
            // el := mload(loc)

            let loc := add(data, sub(mul(8, index), 24))
            el := and(mload(loc), 0xffffffff)

            // // Clean the bits by shifting by `32 - (32 >> scale)) * 8`.
            // let shft := shl(3, sub(32, sz))
            // el := shr(shft, shl(shft, el))
        }
    }

    function at(SM32x32 A, uint256 i, uint256 j) internal pure returns (uint256 el) {
        (uint256 n, uint256 m, uint256 data,) = header(A);

        require(i < n && j < m, "SolMat: out of bounds");

        assembly {
            // let loc := add(data, mul(DATA_BYTES, add(mul(i, m), j)))
            // el := mload(loc)
            let loc := add(data, sub(mul(8, add(mul(i, m), j)), 24))
            el := and(mload(loc), 0xffffffff)
        }
    }

    function set(SM32x32 A, uint256 index, uint256 value) internal pure {
        (uint256 n, uint256 m, uint256 data,) = header(A);

        unchecked {
            require(index < n * m, "SolMat: out of bounds");
        }

        assembly {
            // let slt := index &
            let loc := add(data, sub(mul(8, index), 24))
            let el := mload(loc)

            mstore(loc, or(and(value, 0xffffffff), and(el, not(0xffffffff))))
            // // Wipe previous slot.
            // // and(data, not(shl(shl(5, sub(7, i)), 0xffffffff))),
            // shr(5, shl(5, data)),
            // // write data to slot.
            // shl(shl(5, sub(7, and(index, 7))), and(value, 0xffffffff))
        }

        // assembly {
        //     // NOTE: need to load and merge
        //     let loc := add(data, mul(0x10, index))
        //     let el := mload(loc)
        //     // mstore(loc, value << 7)
        //     mstore(loc, value)
        // }
    }

    function set(SM32x32 A, uint256 i, uint256 j, uint256 value) internal pure {
        (uint256 n, uint256 m, uint256 data,) = header(A);

        require(i < n && j < m, "SolMat: out of bounds");

        assembly {
            let loc := add(data, mul(DATA_BYTES, add(mul(i, m), j)))
            mstore(loc, value)
        }
    }

    /* ------------- functions ------------- */

    function add(SM32x32 A, uint256 a) internal pure returns (SM32x32 C) {
        (uint256 An, uint256 Am, uint256 Adata, uint256 Asz) = header(A);

        C = zeros(An, Am);
        uint256 Cdata = ref(C);

        assembly {
            let i
            for {} lt(i, An) {} {
                let j
                for {} lt(j, Am) {} {
                    let el1 := mload(add(Adata, mul(Asz, add(mul(i, Am), j))))
                    let s := add(el1, a)

                    mstore(add(Cdata, mul(Asz, add(mul(i, Am), j))), s)

                    j := add(1, j)
                }

                i := add(1, i)
            }
        }
    }

    function mul(SM32x32 A, uint256 a) internal pure returns (SM32x32 C) {
        (uint256 An, uint256 Am, uint256 Adata, uint256 Asz) = header(A);

        C = zeros(An, Am);
        uint256 Cdata = ref(C);

        assembly {
            let i
            for {} lt(i, An) {} {
                let j
                for {} lt(j, Am) {} {
                    let el := mload(add(Adata, mul(Asz, add(mul(i, Am), j))))
                    let pr := mul(el, a)

                    mstore(add(Cdata, mul(Asz, add(mul(i, Am), j))), pr)

                    j := add(1, j)
                }

                i := add(1, i)
            }
        }
    }

    function add(SM32x32 A, SM32x32 B) internal pure returns (SM32x32 C) {
        (uint256 An, uint256 Am, uint256 Adata, uint256 Asz) = header(A);
        (uint256 Bn, uint256 Bm, uint256 Bdata, uint256 Bsz) = header(B);

        require(An == Bn && Am == Bm, "SolMat: invalid dimensions");
        require(Asz == Bsz, "SolMat: invalid size");

        C = zeros(An, Am);
        uint256 Cdata = ref(C);

        assembly {
            let i
            for {} lt(i, An) {} {
                let j
                for {} lt(j, Am) {} {
                    let el1 := mload(add(Adata, mul(Asz, add(mul(i, Am), j))))
                    let el2 := mload(add(Bdata, mul(Bsz, add(mul(i, Bm), j))))

                    let s := add(el1, el2)

                    mstore(add(Cdata, mul(Asz, add(mul(i, Am), j))), s)

                    j := add(1, j)
                }

                i := add(1, i)
            }
        }
    }

    function dot(SM32x32 A, SM32x32 B) internal pure returns (SM32x32 C) {
        (uint256 An, uint256 Am, uint256 Adata, uint256 Asz) = header(A);
        (uint256 Bn, uint256 Bm, uint256 Bdata, uint256 Bsz) = header(B);

        require(Am == Bn, "SolMat: invalid dimensions");
        require(Asz == Bsz, "SolMat: invalid size");

        C = zeros(An, Bm);
        uint256 Cdata = ref(C);

        assembly {
            let i
            for {} lt(i, An) {} {
                let j
                for {} lt(j, Bm) {} {
                    let k
                    let d
                    for {} lt(k, Am) {} {
                        let el1 := mload(add(Adata, mul(Asz, add(mul(i, Am), k))))
                        let el2 := mload(add(Bdata, mul(Bsz, add(mul(k, Bm), j))))

                        d := add(d, mul(el1, el2))
                        k := add(1, k)
                    }
                    // @note what size does this end up?
                    mstore(add(Cdata, mul(Asz, add(mul(i, Bm), j))), d)

                    j := add(1, j)
                }

                i := add(1, i)
            }
        }
    }

    function eq(SM32x32 A, uint256 value) internal pure returns (bool equals) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

        equals = true;

        unchecked {
            for (uint256 i; i < n && equals; ++i) {
                for (uint256 j; j < m && equals; ++j) {
                    assembly {
                        let loc := add(data, mul(sz, add(mul(i, m), j)))
                        equals := eq(mload(loc), value)
                    }
                }
            }
        }
    }

    // function eq(SM32x32 A, SM32x32 B) internal pure returns (SM32x32 C) {
    function eq(SM32x32 A, SM32x32 B) internal pure returns (bool equals) {
        if (SM32x32.unwrap(A) == SM32x32.unwrap(B)) return true;

        (uint256 An, uint256 Am, uint256 Adata, uint256 Asz) = header(A);
        (uint256 Bn, uint256 Bm, uint256 Bdata, uint256 Bsz) = header(B);

        // require(An == Bn && Am == Bm, "SolMat: invalid dimensions");
        // require(Asz == Bsz, "SolMat: invalid size");

        equals = An == Bn && Am == Bm;

        assembly {
            let i
            for {} lt(i, An) {} {
                let j
                for {} lt(j, Am) {} {
                    let el1 := mload(add(Adata, mul(Asz, add(mul(i, Am), j))))
                    let el2 := mload(add(Bdata, mul(Bsz, add(mul(i, Bm), j))))

                    equals := eq(el1, el2)

                    if iszero(equals) { break }

                    j := add(1, j)
                }

                if iszero(equals) { break }

                i := add(1, i)
            }
        }
    }

    function sum(SM32x32 A) internal pure returns (uint256 res) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

        unchecked {
            for (uint256 i; i < n; ++i) {
                for (uint256 j; j < m; ++j) {
                    assembly {
                        let loc := add(data, mul(sz, add(mul(i, m), j)))
                        res := add(res, mload(loc))
                    }
                }
            }
        }
    }
}
