// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type USM256 is uint256;

using {
    sum,
    header,
    shape,
    dim0,
    dim1,
    length,
    sizeBytes,
    ref,
    reshape,
    _bytes,
    copy,
    at,
    atIndex,
    set,
    setIndex,
    add,
    addScalar,
    mulScalar,
    add,
    dot,
    eq,
    eqScalar,
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

error USM256_TooLarge();
error USM256_InvalidRange();
error USM256_IndexOutOfBounds();
error USM256_InvalidDimensions();
error USM256_IncompatibleDimensions();

/* ------------- header ------------- */

function USM256Header(uint256 data, uint256 n, uint256 m) pure returns (USM256 A) {
    A = USM256.wrap(
        data << 48 // data location
            | m << 24 | n // shape
    );

    if ((n | m | (data >> 40)) > MAX_24_BITS) revert USM256_TooLarge();
}

function header(USM256 A) pure returns (uint256 n, uint256 m, uint256 data) {
    n = (USM256.unwrap(A)) & MAX_24_BITS;
    m = (USM256.unwrap(A) >> 24) & MAX_24_BITS;
    data = (USM256.unwrap(A) >> 48) & MAX_64_BITS;
}

function shape(USM256 A) pure returns (uint256 n, uint256 m) {
    n = (USM256.unwrap(A)) & MAX_24_BITS;
    m = (USM256.unwrap(A) >> 24) & MAX_24_BITS;
}

function dim0(USM256 A) pure returns (uint256 n) {
    n = (USM256.unwrap(A)) & MAX_24_BITS;
}

function dim1(USM256 A) pure returns (uint256 m) {
    m = (USM256.unwrap(A) >> 24) & MAX_24_BITS;
}

function length(USM256 A) pure returns (uint256 len) {
    unchecked {
        uint256 n = (USM256.unwrap(A)) & MAX_24_BITS;
        uint256 m = (USM256.unwrap(A) >> 24) & MAX_24_BITS;

        len = n * m;
    }
}

function sizeBytes(USM256 A) pure returns (uint256 size) {
    unchecked {
        uint256 n = (USM256.unwrap(A)) & MAX_24_BITS;
        uint256 m = (USM256.unwrap(A) >> 24) & MAX_24_BITS;

        size = n * m * 32;
    }
}

function ref(USM256 A) pure returns (uint256 data) {
    data = (USM256.unwrap(A) >> 48) & MAX_64_BITS;
}

/* ------------- malloc ------------- */

function malloc(uint256 size) pure returns (uint256 ptr) {
    assembly {
        // Load free memory pointer.
        ptr := mload(0x40)

        // Update free memory pointer.
        mstore(0x40, add(ptr, size))
        // mstore(0x40, add(ptr, and(add(size, 0x1f), not(0x1f))))
    }
}

/* ------------- constructors ------------- */

function zerosUnsafe(uint256 n, uint256 m) pure returns (USM256 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 32;
        // Allocate memory space for matrix.
        // Add 32 bytes to store the byte size.
        uint256 data = malloc(32 + size);

        assembly {
            // Store the bytes size.
            mstore(data, size)
        }

        // Generate metadata header, skip the 32 bytes length.
        // This is only for convenience when converting to `bytes`.
        A = USM256Header(data + 32, n, m);
    }
}

function zeros(uint256 n, uint256 m) pure returns (USM256 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 32;
        // Allocate memory space for matrix.
        // Add 32 bytes to store the byte size.
        uint256 data = malloc(32 + size);

        assembly {
            // Store the bytes size.
            mstore(data, size)
        }

        // Skip the 32 bytes length.
        data = data + 32;

        assembly {
            // Get pointer to data location.
            let ptr := data
            // We end after n * m elements * 32 bytes.
            let end := add(ptr, mul(mul(n, m), 32))

            // Iterate over all elements and store `0`s.
            // We cannot know for sure whether these are cleared.
            for {} lt(ptr, end) {} {
                // Store `0` at current pointer location.
                mstore(ptr, 0)
                // Advance pointer to next slot.
                ptr := add(ptr, 32)
            }
        }

        // Generate metadata header.
        A = USM256Header(data, n, m);
    }
}

function ones(uint256 n, uint256 m) pure returns (USM256 A) {
    // We can unsafely allocate a new matrix,
    // because we will write to all memory slots.
    A = zerosUnsafe(n, m);

    // Obtain a reference to matrix data location.
    uint256 ptr = ref(A);

    assembly {
        // We end after n * m elements * 32 bytes.
        let end := add(ptr, mul(mul(n, m), 32))

        // Iterate over all elements and store `1`s.
        for {} lt(ptr, end) {} {
            // Store `1` at current pointer location.
            mstore(ptr, 1)
            // Advance pointer to next slot.
            ptr := add(ptr, 32)
        }
    }
}

function eye(uint256 n, uint256 m) pure returns (USM256 A) {
    A = zerosUnsafe(n, m);

    uint256 len = (n < m) ? n : m;

    // Obtain a reference to matrix data location.
    uint256 ptr = ref(A);

    assembly {
        // We end after n * m elements * 32 bytes.
        let end := add(ptr, mul(mul(len, m), 32))

        // TODO: fix, overwrite all elements.
        // Iterate over all elements.
        for {} lt(ptr, end) {} {
            // Store `1` at current pointer location.
            mstore(ptr, 1)
            ptr := add(ptr, mul(32, add(1, m)))
            // Advance pointer to next slot.
            // ptr := add(ptr, 32)
        }
    }
}

function range(uint256 start, uint256 end) pure returns (USM256 A) {
    unchecked {
        if (start > end) revert USM256_InvalidRange();

        uint256 numElements = end - start;

        // We can unsafely allocate a new matrix,
        // because we will write to all memory slots.
        A = zerosUnsafe(1, numElements);

        // Obtain a reference to matrix data location.
        uint256 ptr = ref(A);

        assembly {
            let i
            // Iterate over all elements.
            for {} lt(i, numElements) {} {
                // Store `i` at current pointer location.
                mstore(ptr, add(start, i))
                // Advance pointer to next slot.
                ptr := add(ptr, 32)
                i := add(i, 1)
            }
        }
    }
}

function range(uint256 end) pure returns (USM256 A) {
    return range(0, end);
}

function reshape(USM256 A, uint256 nNew, uint256 mNew) pure returns (USM256 out) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (n * m != nNew * mNew) revert USM256_InvalidDimensions();

        out = USM256Header(data, nNew, mNew);
    }
}

/* ------------- indexing ------------- */

function atIndex(USM256 A, uint256 index) pure returns (uint256 el) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (index >= n * m) revert USM256_IndexOutOfBounds();

        assembly {
            let loc := add(data, mul(32, index))
            el := mload(loc)
        }
    }
}

function setIndex(USM256 A, uint256 index, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (index >= n * m) revert USM256_IndexOutOfBounds();

        assembly {
            let loc := add(data, mul(32, index))
            mstore(loc, value)
        }
    }
}

function at(USM256 A, uint256 i, uint256 j) pure returns (uint256 el) {
    (uint256 n, uint256 m, uint256 data) = header(A);

    if (i >= n || j >= m) revert USM256_IndexOutOfBounds();

    assembly {
        let loc := add(data, mul(32, add(mul(i, m), j)))
        el := mload(loc)
    }
}

function set(USM256 A, uint256 i, uint256 j, uint256 value) pure {
    (uint256 n, uint256 m, uint256 data) = header(A);

    if (i >= n || j >= m) revert USM256_IndexOutOfBounds();

    assembly {
        let loc := add(data, mul(32, add(mul(i, m), j)))
        mstore(loc, value)
    }
}

/* ------------- functions ------------- */

function addScalar(USM256 A, uint256 s) pure returns (USM256 C) {
    (uint256 n, uint256 m, uint256 data) = header(A);

    C = zerosUnsafe(n, m);

    uint256 dataC = ref(C);

    unchecked {
        uint256 idx;
        uint256 end = n * m * 32;

        while (idx != end) {
            assembly {
                let a := mload(add(data, idx))
                let c := add(a, s)

                mstore(add(dataC, idx), c)
            }

            idx = idx + 32;
        }
    }
}

function mulScalar(USM256 A, uint256 s) pure returns (USM256 C) {
    (uint256 n, uint256 m, uint256 data) = header(A);

    C = zerosUnsafe(n, m);

    uint256 dataC = ref(C);

    unchecked {
        uint256 idx;
        uint256 end = n * m * 32;

        while (idx != end) {
            assembly {
                let a := mload(add(data, idx))
                let c := mul(a, s)

                mstore(add(dataC, idx), c)
            }

            idx = idx + 32;
        }
    }
}

function add(USM256 A, USM256 B) pure returns (USM256 C) {
    (uint256 nA, uint256 mA, uint256 dataA) = header(A);
    (uint256 nB, uint256 mB, uint256 dataB) = header(B);

    if (nA != nB || mA != mB) revert USM256_IncompatibleDimensions();

    C = zerosUnsafe(nA, mA);

    uint256 dataC = ref(C);

    unchecked {
        uint256 idx;
        uint256 end = nA * mA * 32;

        while (idx != end) {
            assembly {
                let a := mload(add(dataA, idx))
                let b := mload(add(dataB, idx))
                let c := add(a, b)

                mstore(add(dataC, idx), c)
            }

            idx = idx + 32;
        }
    }
}

function dot(USM256 A, USM256 B) pure returns (USM256 C) {
    (uint256 nA, uint256 mA, uint256 dataA) = header(A);
    (uint256 nB, uint256 mB, uint256 dataB) = header(B);

    if (mA != nB) revert USM256_IncompatibleDimensions();

    C = zerosUnsafe(nA, mB);

    uint256 dataC = ref(C);

    // assembly {
    //     let i
    //     for {} lt(i, nA) {} {
    //         let j
    //         for {} lt(j, mB) {} {
    //             let k
    //             let d
    //             for {} lt(k, mA) {} {
    //                 let el1 := mload(add(dataA, mul(32, add(mul(i, mA), k))))
    //                 let el2 := mload(add(dataB, mul(32, add(mul(k, mB), j))))

    //                 d := add(d, mul(el1, el2))
    //                 k := add(1, k)
    //             }
    //             mstore(add(dataC, mul(32, add(mul(i, mB), j))), d)

    //             j := add(1, j)
    //         }

    //         i := add(1, i)
    //     }
    // }

    unchecked {
        // Perform the matrix multiplication given by:
        // `C_ij = A_ik B_kj`
        //
        // Given `i`, `j`, `k`, the offsets
        // of the elements in `A`, `B` to be summed are:
        // `idxA = 32 * (k + i * mA)`
        // `idxB = 32 * (j + k * mb)`

        uint256 idxC;
        uint256 idxAStart;

        for (uint256 i; i < nA; ++i) {
            uint256 idxBStart;

            for (uint256 j; j < mB; ++j) {
                uint256 idxA = idxAStart;
                uint256 idxB = idxBStart;

                // Perform the dot product on the current
                // row vector of `A` and the column vector of `B`.
                // Store the result in `c`.
                uint256 c;

                for (uint256 k; k < mA; ++k) {
                    assembly {
                        let a := mload(add(dataA, idxA))
                        let b := mload(add(dataB, idxB))

                        c := add(c, mul(a, b))
                    }

                    idxA = idxA + 32; // The next element is in the next column of `A`.
                    idxB = idxB + 32 * mB; // The next element of `B` is in the row below.
                }

                assembly {
                    mstore(add(dataC, idxC), c)
                }

                idxC = idxC + 32; // Iterate over the elements of `C`.
                idxBStart = idxBStart + 32; // Start at the next column of `B`.
            }

            idxAStart = idxAStart + 32 * mA; // Jump to the next row of `A`.
        }
    }

    // unchecked {
    //     uint256 idxC;
    //     uint256 idxAStart;

    //     for (uint256 i; i < nA; ++i) {
    //         // idxA = 32 * (k + i * mA)
    //         // idxB = 32 * (j + k * mb)

    //         // uint256 idxAStart = 32 * i * mA;
    //         uint256 idxBStart;

    //         for (uint256 j; j < mB; ++j) {
    //             uint256 idxA = idxAStart;
    //             uint256 idxB = idxBStart;

    //             // Perform the dot product on the current
    //             // row vector of `A` and the column vector of `B`.
    //             // Store the result in `c`.
    //             uint256 c;

    //             for (uint256 k; k < mA; ++k) {
    //                 assembly {
    //                     let a := mload(add(dataA, idxA))
    //                     let b := mload(add(dataB, idxB))

    //                     c := add(c, mul(a, b))
    //                 }

    //                 idxA = idxA + 32; // The next element is in the next column of `A`.
    //                 idxB = idxB + 32 * mB; // The next element of `B` is in the row below.
    //             }

    //             assembly {
    //                 mstore(add(dataC, idxC), c)
    //             }

    //             idxC = idxC + 32; // Iterate over the elements of `C`.
    //             idxBStart = idxBStart + 32; // Start at the next column of `B`.
    //         }

    //         idxAStart = idxAStart + 32 * mA; // Jump to the next row of `A`.
    //     }
    // }
}

function sum(USM256 A) pure returns (uint256 res) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assembly {
                    let loc := add(data, mul(32, add(mul(i, m), j)))
                    res := add(res, mload(loc))
                }
            }
        }
    }
}

function eqScalar(USM256 A, uint256 value) pure returns (bool equals) {
    (uint256 n, uint256 m, uint256 data) = header(A);

    equals = true;

    unchecked {
        for (uint256 i; i < n && equals; ++i) {
            for (uint256 j; j < m && equals; ++j) {
                assembly {
                    let loc := add(data, mul(32, add(mul(i, m), j)))
                    let el := mload(loc)

                    equals := eq(el, value)
                }
            }
        }
    }
}

// function eq(USM256 A, USM256 B)  pure returns (USM256 C) {
function eq(USM256 A, USM256 B) pure returns (bool equals) {
    if (USM256.unwrap(A) == USM256.unwrap(B)) return true;

    (uint256 nA, uint256 mA, uint256 dataA) = header(A);
    (uint256 Bn, uint256 Bm, uint256 Bdata) = header(B);

    // require(nA == Bn && mA == Bm, "SolMat: invalid dimensions");
    // require(Asz == Bsz, "SolMat: invalid size");

    equals = nA == Bn && mA == Bm;

    assembly {
        let i
        for {} lt(i, nA) {} {
            let j
            for {} lt(j, mA) {} {
                let el1 := mload(add(dataA, mul(32, add(mul(i, mA), j))))
                let el2 := mload(add(Bdata, mul(32, add(mul(i, Bm), j))))

                equals := eq(el1, el2)

                if iszero(equals) { break }

                j := add(1, j)
            }

            if iszero(equals) { break }

            i := add(1, i)
        }
    }
}

/* ------------- conversions ------------- */

function from_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (USM256 A) {
    unchecked {
        if (n * m * 32 > dataBytes.length) revert USM256_TooLarge();

        uint256 dataA;

        assembly {
            // Actual data is located after length encoding.
            dataA := add(32, dataBytes)
        }

        A = USM256Header(dataA, n, m);
    }
}

function _bytes(USM256 A) pure returns (bytes memory dataBytes) {
    uint256 data = ref(A);

    assembly {
        // This only works under the assumption that
        // we always store the size in bytes before the data.
        dataBytes := sub(data, 32)
    }
}

/// @dev todo: compare gas costs to manual copy
function from(bytes memory dataBytes, uint256 n, uint256 m) view returns (USM256 A) {
    unchecked {
        uint256 size = n * m * 32;
        uint256 dataA = malloc(32 + size);

        assembly {
            // Store bytes size.
            mstore(dataA, size)
            // Actual data will be stored in next mem slot.
            dataA := add(dataA, 32)
            // Use address(4) precompile to copy memory data `dataBytes` to `dataA`.
            pop(staticcall(gas(), 4, add(32, dataBytes), mload(dataBytes), dataA, size))
        }

        A = USM256Header(dataA, n, m);
    }
}

function copy(USM256 A) view returns (USM256 B) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        uint256 size = n * m * 32;
        uint256 dataB = malloc(32 + size);

        assembly {
            // Store bytes size.
            mstore(dataB, size)
            // Actual data will be stored in next mem slot.
            dataB := add(dataB, 32)
            // Use address(4) precompile to copy memory data `dataBytes` to `dataB`.
            pop(staticcall(gas(), 4, data, size, dataB, size))
        }

        B = USM256Header(dataB, n, m);
    }
}

/* ------------- unsafe conversions ------------- */

/// @dev `data` needs to be contiguous in memory.
function fromUnsafe_(uint8[3][4] memory data) pure returns (USM256 A) {
    uint256 ptr;

    assembly {
        // Making a big assumption here that `data` uint8[3] entries
        // are laid out contiguously in memory right after the pointers.
        ptr := mload(data)
        // Store data bytes length in position `ptr - 32`.
        // This allows to easily retrieve the underlying data as bytes,
        // but "destroys" the original `uint8[3][4] memory data` and
        // it should not be used afterwards.
        mstore(sub(ptr, 32), 384)
    }

    A = USM256Header(ptr, 4, 3);
}

function fromUnsafe_(uint8[3][3] memory data) pure returns (USM256 A) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    A = USM256Header(ptr, 3, 3);
}
