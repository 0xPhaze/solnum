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

function USM256Header(uint256 ptr, uint256 n, uint256 m) pure returns (USM256 A) {
    A = USM256.wrap(
        ptr << 48 // data location
            | m << 24 | n // shape
    );

    if ((n | m | (ptr >> 40)) > MAX_24_BITS) revert USM256_TooLarge();
}

function header(USM256 A) pure returns (uint256 n, uint256 m, uint256 ptr) {
    n = (USM256.unwrap(A)) & MAX_24_BITS;
    m = (USM256.unwrap(A) >> 24) & MAX_24_BITS;
    ptr = (USM256.unwrap(A) >> 48) & MAX_64_BITS;
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

function ref(USM256 A) pure returns (uint256 ptr) {
    ptr = (USM256.unwrap(A) >> 48) & MAX_64_BITS;
}

/* ------------- malloc ------------- */

function malloc(uint256 size) pure returns (uint256 ptr) {
    assembly {
        // Load free memory pointer.
        ptr := mload(0x40)

        // Update free memory pointer.
        mstore(0x40, add(ptr, size))
    }
}

/* ------------- constructors ------------- */

function zerosUnsafe(uint256 n, uint256 m) pure returns (USM256 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 32;
        // Allocate memory space for matrix.
        // Add 32 bytes to store the byte size.
        uint256 ptr = malloc(32 + size);

        assembly {
            // Store the bytes size.
            mstore(ptr, size)
        }

        // Generate metadata header, skip the 32 bytes length.
        // This is only for convenience when converting to `bytes`.
        A = USM256Header(ptr + 32, n, m);
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

        // uint256 idx;
        // uint256 end = n * m * 32;
        // uint256 dataC = ref(C);

        // while (idx != end) {
        //     assembly {
        //         let a := mload(add(data, idx))
        //         let c := add(a, s)

        //         mstore(add(dataC, idx), c)
        //     }

        //     idx = idx + 32;
        // }

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

function atIndex(USM256 A, uint256 index) pure returns (uint256 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (index >= n * m) revert USM256_IndexOutOfBounds();

        uint256 idx = data + 32 * index;

        assembly {
            a := mload(idx)
        }
    }
}

function setIndex(USM256 A, uint256 index, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (index >= n * m) revert USM256_IndexOutOfBounds();

        uint256 idx = data + 32 * index;

        assembly {
            mstore(idx, value)
        }
    }
}

function at(USM256 A, uint256 i, uint256 j) pure returns (uint256 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (i >= n || j >= m) revert USM256_IndexOutOfBounds();

        uint256 idx = data + 32 * (i * m + j);

        assembly {
            a := mload(idx)
        }
    }
}

function set(USM256 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (i >= n || j >= m) revert USM256_IndexOutOfBounds();

        uint256 idx = data + 32 * (i * m + j);

        assembly {
            mstore(idx, value)
        }
    }
}

/* ------------- Mat x Mat operators ------------- */

function add(USM256 A, USM256 B) pure returns (USM256 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataB) = header(B);

        if (nA != nB || mA != mB) revert USM256_IncompatibleDimensions();

        C = zerosUnsafe(nA, mA);

        uint256 idxA = dataA;
        uint256 idxB = dataB;
        uint256 endA = idxA + nA * mA * 32;
        uint256 idxC = ref(C);

        while (idxA != endA) {
            assembly {
                let a := mload(idxA)
                let b := mload(idxB)
                let c := add(a, b)

                mstore(idxC, c)
            }

            idxA = idxA + 32;
            idxB = idxB + 32;
            idxC = idxC + 32;
        }
    }
}

/// Perform the matrix multiplication given by:
/// `C_ij = A_ik B_kj`
///
/// Given `i`, `j`, `k`, the offsets
/// of the elements in `A`, `B` to be summed are:
/// `idxA = 32 * (k + i * mA)`
/// `idxB = 32 * (j + k * mb)`
///
/// However, it's cheaper to not keep track of `i`, `j`, `k`,
/// but to keep running pointers to the elements of the matrix.
function dot(USM256 A, USM256 B) pure returns (USM256 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataB) = header(B);

        if (mA != nB) revert USM256_IncompatibleDimensions();

        C = zerosUnsafe(nA, mB);

        uint256 dataC = ref(C);

        uint256 idxC;
        uint256 idxARowSize = 32 * mA;
        uint256 idxBRowSize = 32 * mB;

        uint256 idxALastRow = 32 * nA * mA;
        uint256 idxARow; // Updates by row size of `A` in i-loop.

        // Loop over `C`s `i` indices.
        while (idxARow != idxALastRow) {
            // i-loop start.

            uint256 idxBCol = 0;

            while (idxBCol != idxBRowSize) {
                // j-loop start.

                uint256 idxB = idxBCol;
                uint256 idxA = idxARow;
                uint256 idxAInnerEnd = idxARow + idxARowSize;

                // Perform the dot product on the current
                // row vector of `A` and the column vector of `B`.
                // Store the result in `c`.
                uint256 c;

                while (idxA != idxAInnerEnd) {
                    // k-loop start.

                    assembly {
                        let a := mload(add(dataA, idxA)) // Load A[i,k].
                        let b := mload(add(dataB, idxB)) // Load B[k,j].

                        c := add(c, mul(a, b)) // Add the product `a * b` to `c`.
                    }

                    idxA = idxA + 32; // Loop over `A`s columns.
                    idxB = idxB + idxBRowSize; // Loop over `B`s rows.
                }

                assembly {
                    mstore(add(dataC, idxC), c) // Store the result in C[i,j].
                }

                idxC = idxC + 32; // Advance to the next element of `C`.
                idxBCol = idxBCol + 32; // Advance to the next column of `B`.
            }

            idxARow = idxARow + idxARowSize; // Advance to the next row of `A`.
        }
    }
}

function eq(USM256 A, USM256 B) pure returns (bool equals) {
    unchecked {
        if (USM256.unwrap(A) == USM256.unwrap(B)) return true;

        (uint256 nA, uint256 mA, uint256 dataA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataB) = header(B);

        equals = nA == nB && mA == mB;

        uint256 idx;
        uint256 end = nA * mA * 32;

        while (idx != end && equals) {
            assembly {
                let a := mload(add(dataA, idx))
                let b := mload(add(dataB, idx))

                equals := eq(a, b)
            }

            idx = idx + 32;
        }
    }
}

/* ------------- Mat x scalar operators ------------- */

function addScalar(USM256 A, uint256 s) pure returns (USM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        C = zerosUnsafe(n, m);

        uint256 idxA = data;
        uint256 endA = idxA + n * m * 32;
        uint256 idxC = ref(C);

        while (idxA != endA) {
            assembly {
                let a := mload(idxA)
                let c := add(a, s)

                mstore(idxC, c)
            }

            idxA = idxA + 32;
            idxC = idxC + 32;
        }
    }
}

function mulScalar(USM256 A, uint256 s) pure returns (USM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        C = zerosUnsafe(n, m);

        uint256 idxA = data;
        uint256 endA = idxA + n * m * 32;
        uint256 idxC = ref(C);

        while (idxA != endA) {
            assembly {
                let a := mload(idxA)
                let c := mul(a, s)

                mstore(idxC, c)
            }

            idxA = idxA + 32;
            idxC = idxC + 32;
        }
    }
}

/* ------------- Mat operators ------------- */

function sum(USM256 A) pure returns (uint256 s) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        uint256 idxA = data;
        uint256 endA = idxA + n * m * 32;

        while (idxA != endA) {
            assembly {
                s := add(s, mload(idxA))
            }

            idxA = idxA + 32;
        }
    }
}

function eqScalar(USM256 A, uint256 value) pure returns (bool equals) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        equals = true;

        uint256 idxA = data;
        uint256 endA = idxA + n * m * 32;

        while (idxA != endA) {
            assembly {
                equals := eq(mload(idxA), value)
            }

            if (!equals) break;

            idxA = idxA + 32;
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
