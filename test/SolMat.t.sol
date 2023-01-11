// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

// import "solmate/test/utils/mocks/MockERC721.sol";
// import "solmate/test/utils/mocks/MockERC20.sol";

// import "futils/futils.sol";
import "src/SolMat.sol";

function mat3Mult(uint8[3][3] memory mat1, uint8[3][3] memory mat2) returns (uint256[3][3] memory) {
    // multiplies 3x3 matrix with 3x3 matrix
    uint256 r1 = mat1.length; // rows of mat1
    uint256 c1 = mat1[0].length; // columns of mat1
    uint256 c2 = mat2[0].length; // columns of mat2

    uint256[3][3] memory result;

    for (uint256 i = 0; i < r1; ++i) {
        for (uint256 j = 0; j < c2; ++j) {
            for (uint256 k = 0; k < c1; ++k) {
                result[i][j] += mat1[i][k] * mat2[k][j];
            }
        }
    }

    return (result);
}

contract TestMatMul is Test {
    // using futils for *;
    using SolMat for Mat;

    function setUp() public {}

    function assertIsEye(Mat mat) internal {
        (uint256 n, uint256 m) = mat.shape();

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(mat.at(i, j), (i == j) ? 1 : 0);
            }
        }
    }

    /* ------------- constructors ------------- */

    function freeMemPtr() internal returns (uint256 memPtr) {
        assembly {
            memPtr := mload(0x40)
        }
    }

    function logMatHeader(Mat mat) internal {
        bytes32 data;
        assembly {
            data := mload(mat)
        }
        console.logBytes32(data);
    }

    function test_alloc() public {
        uint256 memPtr = freeMemPtr();
        uint256 ptr = SolMat._alloc(3, 3, 32);

        assertEq(freeMemPtr() - memPtr, (3 * 3) * 32);
        assertEq(ptr, memPtr);

        memPtr = freeMemPtr();
        ptr = SolMat._alloc(1, 7, 32);

        assertEq(freeMemPtr() - memPtr, (1 * 7) * 32);
        assertEq(ptr, memPtr);
    }

    function test_zeros() public {
        Mat m1 = SolMat.zeros(3, 3);
        assertTrue(m1.eq(0));

        Mat m2 = SolMat.zeros(1, 7);
        assertTrue(m2.eq(0));

        m2.set(0, 4, 7);
        assertFalse(m2.eq(0));
    }

    function test_header() public {
        Mat mat = SolMat.zeros(3, 4);
        (uint256 n, uint256 m, uint256 data, uint256 sz) = mat.header();

        assertEq(n, 3);
        assertEq(m, 4);
        assertTrue(data != 0);
        assertEq(sz, 32);
    }

    function test_shape() public {
        Mat mat = SolMat.zeros(0, 0);

        (uint256 n, uint256 m) = mat.shape();

        assertEq(n, 0);
        assertEq(m, 0);

        mat = SolMat.zeros(3, 3);

        (n, m) = mat.shape();

        assertEq(n, 3);
        assertEq(m, 3);

        mat = SolMat.zeros(7, 25);

        (n, m) = mat.shape();

        assertEq(n, 7);
        assertEq(m, 25);
    }

    function test_at_set() public {
        Mat mat = SolMat.zeros(3, 4);

        mat.set(0, 3, 3);
        mat.set(1, 2, 12);
        mat.set(2, 0, 20);

        assertEq(mat.at(0, 3), 3);
        assertEq(mat.at(1, 2), 12);
        assertEq(mat.at(2, 0), 20);

        mat.set(2, 0, 7777);

        assertEq(mat.at(2, 0), 7777);
    }

    function test_at_set(uint256 n, uint256 m, uint256 i, uint256 j, uint256 v) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);
        i = bound(i, 0, n - 1);
        j = bound(j, 0, m - 1);

        Mat mat = SolMat.zeros(n, m);

        mat.set(i, j, v);

        assertEq(mat.at(i, j), v);
    }

    function test_eye() public {
        Mat m1 = SolMat.eye(3, 3);

        assertIsEye(m1);
    }

    function test_ones() public {
        Mat m1 = SolMat.ones(3, 4);

        assertTrue(m1.eq(1));
    }

    function test_fromBytes() public {
        uint8[3][3] memory m1 = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];

        Mat m2 = SolMat.fromBytes_(abi.encode(m1), 3, 3);

        for (uint256 i; i < 3; ++i) {
            for (uint256 j; j < 3; ++j) {
                assertEq(m2.at(i, j), m1[i][j]);
            }
        }

        Mat m3 = m2.copy();

        assertTrue(m3.eq(m2));
    }

    function test_asMat() public {
        uint8[3][3] memory m1 = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];

        Mat m2 = SolMat.asMat_(m1);

        for (uint256 i; i < 3; ++i) {
            for (uint256 j; j < 3; ++j) {
                assertEq(m2.at(i, j), m1[i][j]);
            }
        }

        (uint256 n, uint256 m, uint256 data, uint256 sz) = m2.header();

        // uint256 loc;
        // assembly {
        //     loc := m1
        // }
        // mdump(loc, 10);

        assertEq(n, 3);
        assertEq(m, 3);
        assertTrue(data != 0);
        assertEq(sz, 32);

        // logMat(m2);
        // Mat m3 = m2.copy();

        // assertTrue(m3.eq(m2));
    }

    function mdump(uint256 location, uint256 numSlots) internal view {
        bytes32 m;
        for (uint256 i; i < numSlots; i++) {
            assembly {
                m := mload(add(location, mul(0x20, i)))
            }
            console.logBytes2(bytes2(uint16(location + 0x20 * i)));
            console.logBytes32(m);
        }
        console.log();
    }

    /* ------------- conversions ------------- */

    /* ------------- functions ------------- */

    function test_eq() public {
        Mat m1 = SolMat.fromBytes_(abi.encode([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), 3, 3);
        Mat m2 = m1.copy();

        assertTrue(m1.eq(m2));

        m1.set(0, 0, 9);
        assertFalse(m1.eq(m2));

        m2.set(0, 0, 9);
        assertTrue(m1.eq(m2));
    }

    function test_copy() public {
        uint8[3][3] memory m1 = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];

        Mat m2 = SolMat.fromBytes_(abi.encode(m1), 3, 3);

        for (uint256 i; i < 3; ++i) {
            for (uint256 j; j < 3; ++j) {
                assertEq(m2.at(i, j), i * 3 + j + 1);
            }
        }

        Mat m3 = m2.copy();

        assertTrue(m3.eq(m2));
    }

    // function test_mul() public {
    //     // Mat m1 = SolMat.fromBytes_(abi.encode([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), 3, 3);
    //     Mat m1 = SolMat.asMat_([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
    //     Mat m2 = SolMat.fromBytes_(abi.encode([[1, 1, 1], [2, 2, 2], [3, 3, 3]]), 3, 3);
    //     Mat m3 = SolMat.fromBytes_(abi.encode([[14, 14, 14], [32, 32, 32], [50, 50, 50]]), 3, 3);

    //     assertTrue(m1.mul(m2).eq(m3));
    //     assertFalse(m2.mul(m1).eq(m3));
    // }

    /* ------------- logMat ------------- */

    function logMat(Mat mat) public {
        (uint256 n, uint256 m) = mat.shape();

        string memory str = string.concat("\nMat(", vm.toString(n), ",", vm.toString(m), "):\n");

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                str = string.concat(str, string.concat(vm.toString(mat.at(i, j)), "\t"));
            }
            str = string.concat(str, "\n");
        }

        emit log(str);
    }

    function logMat(uint256[3][3] memory mat) public {
        (uint256 n, uint256 m) = (mat.length, mat[0].length);

        string memory str = string.concat("\nMat(", vm.toString(n), ",", vm.toString(m), "):\n");

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                str = string.concat(str, string.concat(vm.toString(mat[i][j]), "\t"));
            }
            str = string.concat(str, "\n");
        }

        emit log(str);
    }

    // function logMem(Mat mat) public {
    //     // (uint256 n, uint256 m) = mat.shape();
    //     (uint256 n, uint256 m, uint256 data, uint256 size) = mat.header();

    //     string memory str = string.concat("\nMem(", vm.toString(n), ",", vm.toString(m), "):\n");

    //     for (uint256 i; i < n; ++i) {
    //         for (uint256 j; j < m; ++j) {
    //             uint256 el;
    //             assembly {
    //                 el := mload(add(data, mul(add(mul(i, m), j), size)))
    //             }
    //             str = string.concat(str, string.concat(vm.toString(el), "\t"));
    //         }
    //         str = string.concat(str, "\n");
    //     }

    //     emit log(str);
    // }
}
