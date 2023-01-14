// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type USM256 is uint256;

using {
    sum,
    header,
    shape,
    dim0,
    diA,
    length,
    sizeBytes,
    ref,
    reshape,
    toBytes,
    copy,
    at,
    atIndex,
    set,
    setIndex,
    add,
    mul,
    add,
    dot,
    eq,
    sum
} for USM256 global;

uint256 constant META_DATA_BITS = 24;
// uint256 constant META_DATA_MAX = 0xffffff; // 24 bits
// uint256 constant META_DATA_MAX = 0xffffffffffffffff; // 24 bits
uint256 constant DATA_CHUNK_SIZE = 0x20;

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
//     uint64 data;
//     uint24 startx;
//     uint24 starty;
//     uint24 endx;
//     uint24 endy;
//     uint8 stridex;
//     uint8 stridey;
//     bool T;
// }

error TooLarge();

/* ------------- header ------------- */

function USM256Header(uint256 data, uint256 n, uint256 m) pure returns (USM256 A) {
    assembly {
        A :=
            or(
                shl(56, data), // data location
                or(shl(24, m), n) // shape
            )
    }

    require((n | m | (data >> 42)) <= MAX_24_BITS, "SolMat: too large");
}

function header(USM256 A) pure returns (uint256 n, uint256 m, uint256 data, uint256 size) {
    assembly {
        n := and(A, MAX_24_BITS)
        m := and(shr(24, A), MAX_24_BITS)
        size := shr(and(shr(48, A), MAX_04_BITS), WORD)
        data := and(shr(56, A), MAX_64_BITS)
    }
}

function shape(USM256 A) pure returns (uint256 n, uint256 m) {
    assembly {
        n := and(A, MAX_24_BITS)
        m := and(shr(24, A), MAX_24_BITS)
    }
}

function dim0(USM256 A) pure returns (uint256 n) {
    assembly {
        n := and(A, MAX_24_BITS)
    }
}

function diA(USM256 A) pure returns (uint256 m) {
    assembly {
        m := and(shr(24, A), MAX_24_BITS)
    }
}

function length(USM256 A) pure returns (uint256 len) {
    assembly {
        let n := and(A, MAX_24_BITS)
        let m := and(shr(24, A), MAX_24_BITS)
        len := mul(n, m)
    }
}

function sizeBytes(USM256 A) pure returns (uint256 size) {
    assembly {
        let n := and(A, MAX_24_BITS)
        let m := and(shr(24, A), MAX_24_BITS)
        let sb := shr(and(shr(48, A), MAX_04_BITS), WORD)
        size := mul(mul(n, m), sb)
    }
}

function ref(USM256 A) pure returns (uint256 data) {
    assembly {
        data := and(shr(56, A), MAX_64_BITS)
    }
}

/* ------------- alloc ------------- */

function _alloc(uint256 n, uint256 m, uint256 scale) pure returns (uint256 data) {
    assembly {
        data := mload(0x40)
        let size := mul(mul(n, m), shr(scale, WORD))

        // Update free memory pointer.
        // Round up to next multiple of 32 bytes.
        mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))
    }
}

function _alloc(uint256 n, uint256 m) pure returns (uint256 data) {
    assembly {
        data := mload(0x40)
        let size := mul(mul(n, m), WORD)

        // Update free memory pointer.
        // Round up to next multiple of 32 bytes.
        mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))
    }
}

function _alloc(uint256 size) pure returns (uint256 data) {
    assembly {
        data := mload(0x40)

        // Update free memory pointer.
        // Round up to next multiple of 32 bytes.
        mstore(0x40, add(data, and(add(size, 0x1f), not(0x1f))))
    }
}

/* ------------- constructors ------------- */

function zeros(uint256 n, uint256 m) pure returns (USM256 A) {
    // Allocate memory space for matrix.
    uint256 data = _alloc(n, m);

    // Generate metadata header.
    A = USM256Header(data, n, m);
}

function zeros(uint256 m) pure returns (USM256 A) {
    // Allocate memory space for matrix.
    uint256 data = _alloc(1, m);

    // Generate metadata header.
    A = USM256Header(data, 1, m);
}

function ones(uint256 n, uint256 m) pure returns (USM256 A) {
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

function ones(uint256 m) pure returns (USM256 A) {
    return ones(1, m);
}

function eye(uint256 n, uint256 m) pure returns (USM256 A) {
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

function range(uint256 start, uint256 end) pure returns (USM256 A) {
    require(start <= end, "SolMat: start <= end");

    uint256 len;

    unchecked {
        len = end - start;
    }

    A = zeros(1, len);

    for (uint256 i; i < len; ++i) {
        // XXX optimize
        unchecked {
            setIndex(A, i, start + i);
        }
    }
}

function range(uint256 end) pure returns (USM256 A) {
    A = zeros(1, end);

    for (uint256 i; i < end; ++i) {
        // XXX optimize
        setIndex(A, i, i);
    }
}

function reshape(USM256 A, uint256 nNew, uint256 mNew) pure returns (USM256 out) {
    (uint256 n, uint256 m, uint256 data,) = header(A);

    unchecked {
        require(n * m == nNew * mNew, "SolMat: invalid dimensions");
    }

    out = USM256Header(data, nNew, mNew);
}

/* ------------- conversions ------------- */

/// @dev `data` needs to be contiguous in memory.
function from(uint8[3][4] memory data) pure returns (USM256 A) {
    uint256 ptr;

    assembly {
        // Making a big assumption here that `data` uint8[3] entries
        // are laid out contiguously in memory right after the pointers.
        ptr := mload(data)
    }

    A = USM256Header(ptr, 4, 3);
}

function from(uint8[3][3] memory data) pure returns (USM256 A) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    A = USM256Header(ptr, 3, 3);
}

/// @dev todo: compare gas costs to manual copy
function from(bytes memory dataBytes, uint256 n, uint256 m) view returns (USM256 A) {
    uint256 size;
    assembly {
        // XXX
        size := mul(DATA_CHUNK_SIZE, mul(n, m))
    }

    uint256 AData = _alloc(size);

    assembly {
        // Use address(4) precompile to copy memory data `dataBytes` to `AData`.
        pop(staticcall(gas(), 4, add(0x20, dataBytes), mload(dataBytes), AData, size))
    }

    A = USM256Header(AData, n, m);
}

function from_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (USM256 A) {
    unchecked {
        require(dataBytes.length <= (n * m * DATA_CHUNK_SIZE), "SolMat: too large");
    }

    uint256 AData;

    assembly {
        AData := add(0x20, dataBytes) // Skip length encoding.
    }

    A = USM256Header(AData, n, m);
}

function toBytes(USM256 A) view returns (bytes memory newData) {
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

function copy(USM256 A) view returns (USM256 out) {
    (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

    uint256 size;

    assembly {
        size := mul(sz, mul(n, m))
    }

    uint256 newData = _alloc(size);

    assembly {
        // Use address(4) precompile to copy memory data `dataBytes` to `newData`.
        pop(staticcall(gas(), 4, data, size, newData, size))
    }

    out = USM256Header(newData, n, m);
}

// function zeros(uint256 n, uint256 m)  pure returns (USM256 A) {
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

function atIndex(USM256 A, uint256 index) pure returns (uint256 el) {
    (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

    unchecked {
        require(index < n * m, "SolMat: out of bounds");
    }

    assembly {
        let loc := add(data, mul(sz, index))
        el := mload(loc)

        // Clean the bits by shifting by `32 - (32 >> scale)) * 8`.
        let shft := shl(3, sub(32, sz))
        el := shr(shft, shl(shft, el))
    }
}

function at(USM256 A, uint256 i, uint256 j) pure returns (uint256 el) {
    (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

    require(i < n && j < m, "SolMat: out of bounds");

    assembly {
        let loc := add(data, mul(sz, add(mul(i, m), j)))
        el := mload(loc)
    }
}

function setIndex(USM256 A, uint256 index, uint256 value) pure {
    (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

    unchecked {
        require(index < n * m, "SolMat: out of bounds");
    }

    assembly {
        let loc := add(data, mul(sz, index))
        mstore(loc, value)
    }
}

function set(USM256 A, uint256 i, uint256 j, uint256 value) pure {
    (uint256 n, uint256 m, uint256 data, uint256 sz) = header(A);

    require(i < n && j < m, "SolMat: out of bounds");

    assembly {
        let loc := add(data, mul(sz, add(mul(i, m), j)))
        mstore(loc, value)
    }
}

/* ------------- functions ------------- */

function addScalar(USM256 A, uint256 a) pure returns (USM256 C) {
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

function mul(USM256 A, uint256 a) pure returns (USM256 C) {
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

function add(USM256 A, USM256 B) pure returns (USM256 C) {
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

function dot(USM256 A, USM256 B) pure returns (USM256 C) {
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

function eqScalar(USM256 A, uint256 value) pure returns (bool equals) {
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

// function eq(USM256 A, USM256 B)  pure returns (USM256 C) {
function eq(USM256 A, USM256 B) pure returns (bool equals) {
    if (USM256.unwrap(A) == USM256.unwrap(B)) return true;

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

function sum(USM256 A) pure returns (uint256 res) {
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
