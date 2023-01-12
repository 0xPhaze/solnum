// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/SolMat.sol";
import "forge-std/Test.sol";
import "./TestMatHelper.sol";

contract TestSolMat is TestMatHelper {
    using SolMat for Mat;

    uint8[3][4] MAT43 = [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]];

    /* ------------- header ------------- */

    function test_header(uint64 data, uint24 n, uint24 m, uint8 scale) public {
        scale = scale % 6;

        uint256 size = 32 >> scale;

        Mat A = SolMat.newHeader(data, n, m, scale);

        (uint256 hn, uint256 hm, uint256 hdata, uint256 hsz) = A.header();

        assertEq(hn, n);
        assertEq(hm, m);
        assertEq(hsz, size);
        assertEq(hdata, data);

        (hn, hm) = A.shape();

        assertEq(hn, n);
        assertEq(hm, m);

        (hn, hm) = (A.dim0(), A.diA());

        assertEq(hn, n);
        assertEq(hm, m);

        uint256 len = A.length();
        uint256 ref = A.ref();
        uint256 sizeBytes = A.sizeBytes();

        assertEq(len, uint256(n) * uint256(m));
        assertEq(ref, data);
        assertEq(sizeBytes, uint256(n) * uint256(m) * size);
    }

    /* ------------- alloc ------------- */

    function test_alloc(uint8 sz) public {
        uint256 size = (uint256(sz) + 31) / 32 * 32;
        uint256 memPtr = freeMemPtr();

        uint256 ptr = SolMat._alloc(sz);

        assertEq(freeMemPtr() - memPtr, size);
        assertEq(ptr, memPtr);
    }

    function test_alloc(uint8 n, uint8 m) public {
        uint256 size = uint256(n) * uint256(m) * 32;
        uint256 memPtr = freeMemPtr();

        uint256 ptr = SolMat._alloc(n, m);

        assertEq(freeMemPtr() - memPtr, size);
        assertEq(ptr, memPtr);
    }

    function test_alloc(uint8 n, uint8 m, uint8 scale) public {
        uint256 size = (uint256(n) * uint256(m) * uint256(32 >> scale) + 31) / 32 * 32;
        uint256 memPtr = freeMemPtr();

        uint256 ptr = SolMat._alloc(n, m, scale);

        assertEq(freeMemPtr() - memPtr, size);
        assertEq(ptr, memPtr);
    }

    /* ------------- constructors ------------- */

    function test_zeros(uint8 n, uint8 m) public {
        Mat A = SolMat.zeros(n, m);

        assertEq(A, 0);

        // if (n * m != 0) {
        //     A.set(111 % n, 333 % m, 1);
        //     assertFalse(A.eq(0));
        // }
    }

    function test_eye() public {
        Mat A = SolMat.eye(3, 3);

        assertIsEye(A);
    }

    function test_ones() public {
        Mat A = SolMat.ones(3, 4);

        assertTrue(A.eq(1));
    }

    /* ------------- set ------------- */

    function test_set(uint256 n, uint256 m, uint8[3] calldata i, uint8[3] calldata j, uint8[3] calldata v) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        Mat A = SolMat.zeros(n, m);

        A.set(i[0] % n, j[0] % m, v[0]);
        assertEq(A.at(i[0] % n, j[0] % m), v[0]);

        A.set(i[1] % n, j[1] % m, v[1]);
        assertEq(A.at(i[1] % n, j[1] % m), v[1]);

        A.set(i[2] % n, j[2] % m, v[2]);
        assertEq(A.at(i[2] % n, j[2] % m), v[2]);
    }

    function test_range() public {
        Mat A = SolMat.range(1, 13);

        for (uint256 i; i < 12; i++) {
            assertEq(A.at(i), 1 + i);
        }
    }

    function test_reshape() public {
        Mat A = SolMat.range(1, 13);
        Mat B = SolMat.from([[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]]);

        assertEq(A.reshape(4, 3), B);
        assertNEq(A.reshape(3, 4), B);

        // todo: test negative cases
    }

    // function test_xxx() public view {
    //     for (uint256 i; i < 6; i++) {
    //         console.log("%s: %s (%s)", i, 32 >> i, (32 - (32 >> i)) * 8);
    //     }
    // }

    function test_scale() public {
        Mat A = SolMat.range(0, 10);
        Mat B = SolMat.newHeader(A.ref(), 1, 10, 1);

        for (uint256 i; i < 10; i++) {
            assertEq(B.at(i), i % 2 == 0 ? (1 + i) / 2 : 0);
        }
    }

    /* ------------- conversions ------------- */

    function test_from() public {
        Mat A = SolMat.from([[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]]);

        (uint256 n, uint256 m) = (4, 3);

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(A.at(i, j), MAT43[i][j]);
            }
        }

        (uint256 hn, uint256 hm, uint256 hdata, uint256 hsz) = A.header();

        assertEq(hn, n);
        assertEq(hm, m);
        assertEq(hsz, 32);
        assertTrue(hdata != 0);
    }

    function test_from_bytes() public {
        Mat A = SolMat.from(MAT43);
        Mat B = SolMat.from_(abi.encode(MAT43), 4, 3);

        (uint256 An, uint256 Am, uint256 Adata, uint256 Asz) = A.header();
        (uint256 Bn, uint256 Bm, uint256 Bdata, uint256 Bsz) = B.header();

        assertEq(An, Bn);
        assertEq(Am, Bm);
        assertEq(Asz, Bsz);

        assertEq(A, B);

        assertTrue(Adata != 0);
        assertTrue(Bdata != 0);
        assertTrue(Adata != Bdata);
    }

    function test_toBytes() public {
        Mat A = SolMat.from(MAT43);
        Mat B = SolMat.from_(A.toBytes(), 4, 3);

        assertEq(A, B);
        assertTrue(A.ref() != B.ref());
    }

    function test_copy() public {
        Mat A = SolMat.from(MAT43);
        Mat B = A.copy();

        assertEq(A, B);
        assertTrue(A.ref() != B.ref());
    }

    /* ------------- functions ------------- */

    function test_eq() public {
        Mat A = SolMat.from_(abi.encode([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), 3, 3);
        Mat B = A.copy();

        assertEq(A, B);

        A.set(0, 0, 9);
        assertFalse(A.eq(B));

        B.set(0, 0, 9);
        assertEq(A, B);
    }

    function test_dot() public {
        Mat A = SolMat.from([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        Mat B = SolMat.from([[1, 1, 1], [2, 2, 2], [3, 3, 3]]);
        Mat C = SolMat.from([[14, 14, 14], [32, 32, 32], [50, 50, 50]]);

        assertEq(A.dot(B), C);
        assertNEq(B.dot(A), C);
    }

    function test_mul() public {
        Mat A = SolMat.from([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        Mat B = SolMat.from([[2, 4, 6], [8, 10, 12], [14, 16, 18]]);

        assertEq(A.mul(2), B);
    }

    function test_add() public {
        Mat A = SolMat.from([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        Mat B = SolMat.from([[1, 1, 1], [2, 2, 2], [3, 3, 3]]);
        Mat C = SolMat.from([[2, 3, 4], [6, 7, 8], [10, 11, 12]]);

        assertEq(A.add(B), C);
        assertEq(A.add(SolMat.zeros(3, 3)), A);
    }

    function test_add_scalar() public {
        Mat A = SolMat.range(1, 10);

        assertEq(A.add(1), SolMat.range(2, 11));
        assertEq(A.add(10), SolMat.range(11, 20));
    }

    /* ------------- performance ------------- */

    // function test__perf_dot_128() public pure {
    //     Mat A = SolMat.eye(128, 128);
    //     Mat B = SolMat.eye(128, 128);

    //     A.dot(B);
    // }

    // function test__perf_dot_128_x2() public {
    //     Mat A = SolMat.eye(128, 128, 1);
    //     Mat B = SolMat.eye(128, 128, 1);

    //     // A.dot(B);

    //     assertEq(A.dot(B), A);
    // }

    function test_half_prec() public {
        Mat A = SolMat.eye(5, 5, 1);
        Mat B = SolMat.eye(5, 5, 1);

        assertEq(A.dot(B), A);
    }

    function test_range_half() public {
        Mat A = SolMat.range(1, 13);

        for (uint256 i; i < 12; i++) {
            assertEq(A.at(i), 1 + i);
        }
    }

    function test_reshape_half() public {
        Mat A = SolMat.range(1, 13);
        Mat B = SolMat.from([[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]]);

        assertEq(A.reshape(4, 3), B);
        assertNEq(A.reshape(3, 4), B);

        // todo: test negative cases
    }
}
