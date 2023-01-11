// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type Mat is uint256;

library SolMat {
    uint256 constant META_DATA_BITS = 32;
    uint256 constant META_DATA_MAX = 0xffffffff;
    uint256 constant DATA_CHUNK_SIZE = 0x20;

    /* ------------- header ------------- */

    // struct matHeader {
    //     uint24 n;
    //     uint24 m; // 48
    //     uint8 sz; // 1 = 256; 2 = 128
    //     uint64 data; // 64 + 8 = 120
    //     uint24 startx;
    //     uint24 starty;
    //     uint24 endx;
    //     uint24 endy; // 96 = 216
    //     uint8 stridex;
    //     uint8 stridey; // = 232
    //     bool T;
    // }

    function matHeader(uint256 data, uint256 n, uint256 m, uint256 size) internal pure returns (Mat mat) {
        // note: loading does not take into acc diff sizes

        assembly {
            mat :=
                or(
                    or(
                        shl(mul(4, META_DATA_BITS), size), // data chunk size
                        shl(mul(2, META_DATA_BITS), data) // data location
                    ),
                    or(shl(META_DATA_BITS, m), n) // shape
                )
        }

        require((data | n | m) <= META_DATA_MAX, "SolMat: too large");
    }

    function header(Mat mat) internal pure returns (uint256 n, uint256 m, uint256 data, uint256 sz) {
        assembly {
            n := and(mat, META_DATA_MAX)
            m := and(shr(32, mat), META_DATA_MAX)
            data := and(shr(64, mat), META_DATA_MAX)
            sz := and(shr(128, mat), META_DATA_MAX)
        }
    }

    function shape(Mat mat) internal pure returns (uint256 n, uint256 m) {
        assembly {
            n := and(mat, META_DATA_MAX)
            m := and(shr(32, mat), META_DATA_MAX)
        }
    }

    function dim0(Mat mat) internal pure returns (uint256 n) {
        assembly {
            n := and(mat, META_DATA_MAX)
        }
    }

    function dim1(Mat mat) internal pure returns (uint256 m) {
        assembly {
            m := and(shr(32, mat), META_DATA_MAX)
        }
    }

    function length(Mat mat) internal pure returns (uint256 len) {
        assembly {
            let n := and(mat, META_DATA_MAX)
            let m := and(shr(32, mat), META_DATA_MAX)
            len := mul(n, m)
        }
    }

    function size(Mat mat) internal pure returns (uint256 size) {
        assembly {
            let n := and(mat, META_DATA_MAX)
            let m := and(shr(32, mat), META_DATA_MAX)
            let sz := and(shr(128, mat), META_DATA_MAX)
            size := mul(mul(n, m), sz)
        }
    }

    function dataPtr(Mat mat) internal pure returns (uint256 data) {
        assembly {
            data := and(shr(64, mat), META_DATA_MAX)
        }
    }

    /* ------------- constructors ------------- */

    /// @dev `data` needs to be contiguous in memory.
    function asMat_(uint8[3][3] memory data) internal pure returns (Mat mat) {
        uint256 dataPtr;

        assembly {
            // Making a big assumption here that `data` uint8[3] entries
            // are laid out contiguously in memory right after the pointers.
            // dataPtr := add(mul(0x20, 3), data)
            dataPtr := mload(data)
        }

        mat = matHeader(dataPtr, 3, 3, DATA_CHUNK_SIZE);
    }

    function _alloc(uint256 n, uint256 m, uint256 size) internal pure returns (uint256 data) {
        assembly {
            data := mload(0x40)

            // Update free memory pointer.
            // Round up to next multiple of 32 bytes.
            mstore(0x40, add(data, and(add(mul(size, mul(n, m)), 0x1f), not(0x1f))))
            // mstore(0x40, add(data, mul(size, mul(n, m))))
        }
    }

    function _alloc(uint256 size) internal pure returns (uint256 data) {
        assembly {
            data := mload(0x40)
            mstore(0x40, add(data, size))
        }
    }

    function zeros(uint256 n, uint256 m) internal pure returns (Mat mat) {
        // Allocate memory space for matrix.
        // Hardcoding `size` for now.
        uint256 data = _alloc(n, m, DATA_CHUNK_SIZE);

        // Generate metadata header.
        mat = matHeader(data, n, m, DATA_CHUNK_SIZE);
    }

    function ones(uint256 n, uint256 m) internal pure returns (Mat mat) {
        mat = zeros(n, m);

        uint256 size = DATA_CHUNK_SIZE;
        uint256 ptr = dataPtr(mat);

        assembly {
            let len := mul(n, m)
            let end := add(ptr, mul(mul(len, m), size))

            for {} lt(ptr, end) {} {
                mstore(ptr, 1)
                ptr := add(ptr, size)
            }
        }
    }

    function eye(uint256 n, uint256 m) internal pure returns (Mat mat) {
        mat = zeros(n, m);

        uint256 size = DATA_CHUNK_SIZE;
        uint256 len = (n < m) ? n : m;
        uint256 ptr = dataPtr(mat);

        assembly {
            let end := add(ptr, mul(mul(len, m), size))

            for {} lt(ptr, end) {} {
                mstore(ptr, 1)
                ptr := add(ptr, mul(size, add(1, m)))
            }
        }
    }

    /// @dev todo: compare gas costs to manual copy
    function fromBytes(bytes memory dataBytes, uint256 n, uint256 m) internal view returns (Mat mat) {
        uint256 sizeBytes;
        assembly {
            sizeBytes := mul(DATA_CHUNK_SIZE, mul(n, m))
        }

        uint256 matData = _alloc(sizeBytes);

        assembly {
            // Use address(4) precompile to copy memory data `dataBytes` to `matData`.
            pop(staticcall(gas(), 4, add(0x20, dataBytes), mload(dataBytes), matData, sizeBytes))
        }

        mat = matHeader(matData, n, m, DATA_CHUNK_SIZE);
    }

    function fromBytes_(bytes memory dataBytes, uint256 n, uint256 m) internal pure returns (Mat mat) {
        unchecked {
            require(dataBytes.length <= (n * m * DATA_CHUNK_SIZE), "SolMat: too large");
        }

        uint256 matData;

        assembly {
            matData := add(0x20, dataBytes) // Skip length encoding.
        }

        mat = matHeader(matData, n, m, DATA_CHUNK_SIZE);
    }

    function copy(Mat mat) internal view returns (Mat out) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

        uint256 sizeBytes;

        assembly {
            sizeBytes := mul(sz, mul(n, m))
        }

        uint256 newData = _alloc(sizeBytes);

        assembly {
            // Use address(4) precompile to copy memory data `dataBytes` to `newData`.
            pop(staticcall(gas(), 4, data, sizeBytes, newData, sizeBytes))
        }

        out = matHeader(newData, n, m, DATA_CHUNK_SIZE);
    }

    // function zeros(uint256 n, uint256 m) internal pure returns (Mat mat) {
    //     uint256 data;
    //     uint256 size = DATA_CHUNK_SIZE; // Hardcoding for now.
    //     // note: loading does not take into acc diff sizes

    //     assembly {
    //         mat := mload(0x40)
    //         data := add(0x20, mat)

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

    //         mstore(mat, meta)

    //         // Update free memory pointer.
    //         // Round up to next multiple of 32 bytes.
    //         // mstore(0x40, add(data, and(add(mul(size, len), 0x1f), not(0x1f))))
    //         mstore(0x40, add(data, mul(size, len)))
    //     }

    //     require((data | n | m) <= META_DATA_MAX, "SolMat: too large");
    // }

    /* ------------- indexing ------------- */

    function at(Mat mat, uint256 index) internal pure returns (uint256 el) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

        unchecked {
            require(index < n * m, "SolMat: out of bounds");
        }

        assembly {
            let loc := add(data, mul(sz, index))
            el := mload(loc)
        }
    }

    function at(Mat mat, uint256 i, uint256 j) internal pure returns (uint256 el) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

        require(i < n && j < m, "SolMat: out of bounds");

        assembly {
            let loc := add(data, mul(sz, add(mul(i, m), j)))
            el := mload(loc)
        }
    }

    function set(Mat mat, uint256 index, uint256 value) internal pure {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

        unchecked {
            require(index < n * m, "SolMat: out of bounds");
        }

        assembly {
            let loc := add(data, mul(sz, index))
            mstore(loc, value)
        }
    }

    function set(Mat mat, uint256 i, uint256 j, uint256 value) internal pure {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

        require(i < n && j < m, "SolMat: out of bounds");

        assembly {
            let loc := add(data, mul(sz, add(mul(i, m), j)))
            mstore(loc, value)
        }
    }

    /* ------------- functions ------------- */

    function mul(Mat m1, Mat m2) internal pure returns (Mat m3) {
        (uint256 m1n, uint256 m1m, uint256 m1data, uint256 m1sz) = header(m1);
        (uint256 m2n, uint256 m2m, uint256 m2data, uint256 m2sz) = header(m2);

        require(m1m == m2n, "SolMat: invalid dimensions");
        require(m1sz == m2sz, "SolMat: invalid size");

        m3 = zeros(m1n, m2m);

        uint256 m3data = dataPtr(m3);

        assembly {
            let i
            for {} lt(i, m1n) {} {
                let j
                for {} lt(j, m2m) {} {
                    let k
                    let dot
                    for {} lt(k, m1m) {} {
                        let el1 := mload(add(m1data, mul(m1sz, add(mul(i, m1m), k))))
                        let el2 := mload(add(m2data, mul(m2sz, add(mul(k, m2m), j))))

                        dot := add(dot, mul(el1, el2))

                        k := add(1, k)
                    }
                    // @note what size does this end up?
                    mstore(add(m3data, mul(m1sz, add(mul(i, m2m), j))), dot)

                    j := add(1, j)
                }

                i := add(1, i)
            }
        }
    }

    function eq(Mat mat, uint256 value) internal pure returns (bool equals) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

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

    // @note optimize
    function eq(Mat m1, Mat m2) internal pure returns (bool equals) {
        (uint256 m1n, uint256 m1m, uint256 m1data, uint256 m1sz) = header(m1);
        (uint256 m2n, uint256 m2m, uint256 m2data, uint256 m2sz) = header(m2);

        require(m1n == m2n && m1m == m2m, "SolMat: invalid dimensions");

        equals = true;

        unchecked {
            for (uint256 i; i < m1n && equals; ++i) {
                for (uint256 j; j < m1m && equals; ++j) {
                    equals = at(m1, i, j) == at(m2, i, j);
                }
            }
        }
    }

    function sum(Mat mat) internal pure returns (uint256 s) {
        (uint256 n, uint256 m, uint256 data, uint256 sz) = header(mat);

        unchecked {
            for (uint256 i; i < n; ++i) {
                for (uint256 j; j < m; ++j) {
                    assembly {
                        let loc := add(data, mul(sz, add(mul(i, m), j)))
                        s := add(s, mload(loc))
                    }
                }
            }
        }
    }
}

// function mul(Mat memory m1, Mat memory m2) internal returns (Mat memory m3) {
//     uint256 m1_n = m1.n;
//     uint256 m1_m = m1.m;
//     // bool m1_transposed = m1.transposed;
//     bytes m1_data = m1.data;

//     uint256 m2_n = m2.n;
//     uint256 m2_m = m2.m;
//     // bool m2_transposed = m2.transposed;
//     bytes m2_data = m2.data;

//     uint256[3][3] memory result;

//     for (uint256 i = 0; i < r1; ++i) {
//         for (uint256 j = 0; j < c2; ++j) {
//             for (uint256 k = 0; k < c1; ++k) {
//                 result[i][j] += mat1[i][k] * mat2[k][j];
//             }
//         }
//     }
// }
