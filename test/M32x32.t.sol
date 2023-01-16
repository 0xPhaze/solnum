// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/M32x32.sol";
import "src/N32x32.sol";
import "./utils/TestHelper.sol";

contract TestM32x32 is TestHelper {
    uint8[3][3] MATRIX_33 = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
    uint8[3][4] MATRIX_43 = [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]];

    M32x32 memSafeTestMat;

    /* ------------- header ------------- */

    function test_header(uint64 data, uint24 n, uint24 m) public {
        M32x32 A = M32x32Header(data, n, m);
        (uint256 nA, uint256 mA, uint256 dataA) = A.header();

        assertEq(nA, n);
        assertEq(mA, m);
        assertEq(dataA, data);

        (nA, mA) = A.shape();

        assertEq(nA, n);
        assertEq(mA, m);

        (nA, mA) = (A.dim0(), A.dim1());

        assertEq(nA, n);
        assertEq(mA, m);

        assertEq(A.ref(), data);
        assertEq(A.length(), uint256(n) * uint256(m));
        assertEq(A.sizeBytes(), uint256(n) * uint256(m) * 8);
    }

    /* ------------- constructors ------------- */

    function test_zeros(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        uint256 memPtr = freeMemPtr();
        uint256 size = n * m * 8;
        uint256 msize = ((size + 31) / 32) * 32;

        M32x32 A = zeros(n, m);

        assertEq(freeMemPtr() - memPtr, msize + 32);
        assertEq(A.ref(), memPtr + 32);

        (uint256 nA, uint256 mA, uint256 dataA) = A.header();

        // assertEq(A, 0);
        assertEq(nA, n);
        assertEq(mA, m);
        assertEq(dataA, memPtr + 32);
    }

    function test_eye() public {
        M32x32 A = eye(3, 3);

        assertIsEye(A);
    }

    function test_ones(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        M32x32 A = ones(n, m);

        assertEq(A, 1);
    }

    /* ------------- set ------------- */

    function test_setIndex(uint256 n, uint8[10][2] calldata data) public {
        n = bound(n, 1, 10);

        M32x32 A = zeros(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        uint256[10] memory B;

        // Store data at random positions.
        // Apply the same changes to `B`.
        for (uint256 k; k < data.length; k++) {
            uint256 i = data[k][0] % n;
            uint256 v = data[k][1];

            B[i] = v;

            A.setIndex(i, v);
        }

        // Make sure these values can be retrieved again.
        for (uint256 k; k < data.length; k++) {
            uint256 i = data[k][0] % n;

            assertEq(A.atIndex(i), B[i]);
        }
    }

    function test_set(uint256 n, uint256 m, uint8[10][3] calldata data) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        M32x32 A = zeros(n, m);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        uint256[10][10] memory B;

        // Store data at random positions.
        // Apply the same changes to `B`.
        for (uint256 k; k < data.length; k++) {
            uint256 i = data[k][0] % n;
            uint256 j = data[k][1] % m;
            uint256 v = data[k][2];

            B[i][j] = v;

            A.set(i, j, v);
        }

        // Make sure these values can be retrieved again.
        for (uint256 k; k < data.length; k++) {
            uint256 i = data[k][0] % n;
            uint256 j = data[k][1] % m;

            assertEq(A.at(i, j), B[i][j]);
        }
    }

    function test_range(uint256 start, uint256 len) public {
        len = bound(len, 0, 50);
        start = bound(start, 0, 100_000);

        M32x32 A = range(start, start + len);

        for (uint256 i; i < len; i++) {
            assertEq(A.atIndex(i), start + i);
        }
    }

    function test_reshape() public {
        M32x32 A = range(1, 13);
        M32x32 B = range(1, 13);

        assertEq(A.reshape(4, 3), B.reshape(4, 3));
        assertNEq(A.reshape(3, 4), B.reshape(4, 3));
    }

    function test_full(uint256 n, uint256 m, uint64 s) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        M32x32 A = full(n, m, s);

        assertEq(A, s);
    }

    function test_fill(uint256 n, uint256 m, uint64 s) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        M32x32 A = zeros(n, m);
        A.fill_(s);

        assertEq(A, s);
    }

    /* ------------- functions ------------- */

    function test_sum(uint256 n, uint256 m) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        uint256 len = n * m;

        M32x32 A = range(1, len + 1).reshape(n, m);

        assertEq(A.sum(), len * (len + 1) / 2);
    }

    function test_addScalar(uint256 n, uint256 s) public {
        n = bound(n, 1, 20);
        s = bound(s, 1, UINT256_INT64_MAX);

        M32x32 A = zeros(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        assertEq(A.addScalar(s), s);
    }

    function test_addScalarUnchecked(uint256 n, uint256 s) public {
        n = bound(n, 1, 20);
        s = bound(s, 1, UINT64_MAX);

        M32x32 A = zeros(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        assertEq(A.addScalarUnchecked(s), s);
    }

    function test_mulScalar(uint256 n, uint256 s) public {
        n = bound(n, 1, 20);
        s = bound(s, 1, UINT256_INT64_MAX);

        M32x32 A = ones(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        assertEq(A.mulScalar(s), s);
    }

    function test_mulScalarUnchecked(uint256 n, uint256 s) public {
        n = bound(n, 1, 20);
        s = bound(s, 1, UINT64_MAX);

        M32x32 A = ones(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        assertEq(A.mulScalarUnchecked(s), s);
    }

    function test_dot() public {
        // M32x32 A = range(1, 9).reshape(2, 4);
        // M32x32 B = range(10, 18).reshape(4, 2);
        // M32x32 C = fromArray([[uint256(130), 140], [uint256(322), 348]]);

        M32x32 A = fromArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
        M32x32 B = fromArray([[1, 0, 1, 0], [0, 2, 0, 2], [0, 0, 3, 0], [3, 0, 0, 4]]);
        M32x32 C = fromArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

        // M32x32 A = fromArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
        // M32x32 B = fromArray([[5, 6, 6], [7, 7, 8], [8, 9, 9]]);
        // M32x32 C = fromArray([[28, 31, 32], [55, 60, 63], [88, 97, 101]]);

        assertEq(A.dot(B), C);
        // assertNEq(B.dot(A), C);
    }

    function test_dotTransposed() public {
        // M32x32 A = fromArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
        // M32x32 B = fromArray([[5, 6, 6], [7, 7, 8], [8, 9, 9]]);
        // M32x32 C = fromArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

        // assertEq(A.dotTransposed(B), C);
        // assertNEq(B.dotTransposed(A), C);

        M32x32 A = fromArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
        M32x32 B = fromArray([[1, 0, 0, 3], [0, 2, 0, 0], [1, 0, 3, 0], [0, 2, 0, 4]]);
        M32x32 C = fromArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

        assertEq(A.dotTransposed(B), C);
        assertNEq(B.dotTransposed(A), C);
    }

    function test_add(uint256 n) public {
        n = bound(n, 1, 20);

        M32x32 A = range(n);
        M32x32 B = range(n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);
        appendDirtyBits(B);

        assertEq(A.add(B), A.mulScalarUnchecked(2));
        assertEq(A.add(zeros(1, n)), A);
    }

    function test_addUnchecked(uint256 n) public {
        n = bound(n, 1, 20);

        M32x32 A = range(n);
        M32x32 B = range(n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);
        appendDirtyBits(B);

        assertEq(A.addUnchecked(B), A.mulScalarUnchecked(2));
        assertEq(A.addUnchecked(zeros(1, n)), A);
    }

    function test_fromArray() public {
        M32x32 A = fromArray([[1, 2, 3, 4], [5, 6, 7, 8]]);
        M32x32 B = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);

        assertEq(A, range(1, 9).reshape(2, 4));
        assertEq(B, range(1, 10).reshape(3, 3));
    }

    uint256 constant UINT256_INT64_MAX = uint256(uint64(type(int64).max));
    uint256 constant UINT256_INT64_MIN = uint256(uint64(type(int64).min));

    function test_addScalar_revert_overflow(uint256 n) public {
        M32x32 A = ones(1, bound(n, 1, 20));

        vm.expectRevert();
        A.addScalar(UINT256_INT64_MAX);
    }

    function test_addScalar_revert_underflow(uint256 n) public {
        M32x32 A = ones(1, bound(n, 1, 20));

        vm.expectRevert();
        A.addScalar(UINT256_INT64_MIN);
    }

    function test_mulScalar_revert_overflow(uint256 n) public {
        M32x32 A = ones(1, bound(n, 1, 20)).mulScalar(2);

        vm.expectRevert();
        A.mulScalar(UINT256_INT64_MAX);
    }

    function test_mulScalar_revert_underflow(uint256 n) public {
        M32x32 A = ones(1, bound(n, 1, 20)).mulScalar(2);

        vm.expectRevert();
        A.mulScalar(UINT256_INT64_MIN);
    }

    function test_add_revert_overflow(uint256 n) public {
        M32x32 A = ones(1, bound(n, 1, 20));
        M32x32 B = full(1, bound(n, 1, 20), UINT256_INT64_MAX);

        logMat(B);

        vm.expectRevert();
        A.add(B);
    }

    function test_eqScalar(uint256 n, uint256 i) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = ones(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        assertEq(A, 1);

        // Setting any entry to `0`, `A = 1` does not hold.
        A.set(0, i, 0);
        assertFalse(A.eqScalar(1));
    }

    function test_eq(uint256 n, uint256 i) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = range(1, n + 1);
        M32x32 B = range(1, n + 1);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);
        appendDirtyBits(B);

        assertEq(A, B);

        // Setting any entry to `0`, `A = B` does not hold.
        A.set(0, i, 0);
        assertNEq(A, B);
    }

    /* ------------- performance ------------- */

    function test__perf_range_1024() public pure {
        range(1024);
    }

    function test__perf_zeros_128() public pure {
        zeros(128, 128);
    }

    function test__perf_ones_128() public pure {
        ones(128, 128);
    }

    function test__perf_full_128() public pure {
        full(128, 128, 1);
    }

    function test__perf_eye_128() public pure {
        eye(128, 128);
    }

    function test__perf_addScalar_128() public pure {
        M32x32 A = mallocM32x32(128, 128);

        A.addScalar(1);
    }

    // function test__perf_mulScalar_128() public pure {
    //     M32x32 A = mallocM32x32(128, 128);

    //     A.mulScalar(1);
    // }

    function test__perf_addScalarUnchecked_128() public pure {
        M32x32 A = mallocM32x32(128, 128);

        A.addScalarUnchecked(1);
    }

    function test__perf_mulScalarUnchecked_128() public pure {
        M32x32 A = mallocM32x32(128, 128);

        A.mulScalarUnchecked(1);
    }

    function test__perf_eqScalar_128() public pure {
        M32x32 A = mallocM32x32(128, 128);

        A.set(100, 100, 3);

        A.eqScalar(1);
    }

    function test__perf_add_128() public pure {
        M32x32 A = mallocM32x32(128, 128);
        M32x32 B = mallocM32x32(128, 128);

        A.add(B);
    }

    function test__perf_addUnchecked_128() public pure {
        M32x32 A = mallocM32x32(128, 128);
        M32x32 B = mallocM32x32(128, 128);

        A.addUnchecked(B);
    }

    function test__perf_dot_128() public {
        M32x32 A = mallocM32x32(128, 128);
        M32x32 B = mallocM32x32(128, 128);

        A.dot(B);
    }

    function test__perf_dotTransposed_128() public pure {
        M32x32 A = mallocM32x32(128, 128);
        M32x32 B = mallocM32x32(128, 128);

        A.dotTransposed(B);
    }

    function test__perf_sum_128() public pure {
        M32x32 A = mallocM32x32(128, 128);

        A.sum();
    }

    function test__perf_eq_128() public pure {
        M32x32 A = mallocM32x32(128, 128);
        M32x32 B = mallocM32x32(128, 128);

        A.eq(B);
    }

    function test__perf_fill_1024() public pure {
        M32x32 A = mallocM32x32(128, 128);

        A.fill_(1);
    }
}
