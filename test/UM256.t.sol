// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/UM256.sol";
import "./utils/TestHelper.sol";

contract TestUM256 is TestHelper {
    uint8[3][3] MATRIX_33 = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
    uint8[3][4] MATRIX_43 = [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]];

    UM256 memSafeTestMat;

    /* ------------- header ------------- */

    function test_header(uint64 data, uint24 n, uint24 m) public {
        UM256 A = UM256Header(data, n, m);
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
        assertEq(A.sizeBytes(), uint256(n) * uint256(m) * 32);
    }

    /* ------------- malloc ------------- */

    function test_malloc(uint256 sz) public {
        sz = bound(sz, 0, 50);

        uint256 memPtr = freeMemPtr();
        uint256 size = sz * 32;
        uint256 ptr = malloc(size);

        assertEq(freeMemPtr() - memPtr, size);
        assertEq(ptr, memPtr);
    }

    /* ------------- constructors ------------- */

    function test_zeros(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        uint256 memPtr = freeMemPtr();
        uint256 size = n * m * 32;
        UM256 A = zeros(n, m);

        assertEq(freeMemPtr() - memPtr, size + 32);
        assertEq(A.ref(), memPtr + 32);

        (uint256 nA, uint256 mA, uint256 dataA) = A.header();

        assertEq(A, 0);
        assertEq(nA, n);
        assertEq(mA, m);
        assertEq(dataA, memPtr + 32);
    }

    function test_eye() public {
        UM256 A = eye(3, 3);

        assertIsEye(A);
    }

    function test_ones(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        UM256 A = ones(n, m);

        assertEq(A, 1);
    }

    /* ------------- set ------------- */

    function test_set(uint256 n, uint256 m, uint256[10][3] calldata data) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        UM256 A = zeros(n, m);

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

        UM256 A = range(start, start + len);

        for (uint256 i; i < len; i++) {
            assertEq(A.atIndex(i), start + i);
        }
    }

    function test_reshape() public {
        UM256 A = range(1, 13);
        UM256 B = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]]);

        assertEq(A.reshape(4, 3), B);
        assertNEq(A.reshape(3, 4), B);
    }

    function test_fill(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        UM256 A = zeros(n, m);
        A.fill_(123);

        assertEq(A, 123);
    }

    /* ------------- conversions ------------- */

    function test_fromArray() public {
        UM256 A = fromArray(MATRIX_43);
        (uint256 n, uint256 m) = (4, 3);

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(A.at(i, j), MATRIX_43[i][j]);
            }
        }

        (uint256 nA, uint256 mA, uint256 dataA) = A.header();

        assertEq(nA, n);
        assertEq(mA, m);
        assertTrue(dataA != 0);
    }

    function test_fromBytes() public {
        UM256 A = fromArray(MATRIX_43);
        UM256 B = fromBytes(abi.encode(MATRIX_43), 4, 3);

        (uint256 nA, uint256 mA, uint256 dataA) = A.header();
        (uint256 nB, uint256 mB, uint256 dataB) = B.header();

        assertEq(A, B);
        assertEq(nA, nB);
        assertEq(mA, mB);
        assertTrue(dataA != 0);
        assertTrue(dataB != 0);
        assertTrue(dataA != dataB);
    }

    function test_toBytes() public {
        UM256 A = fromArray(MATRIX_43);
        UM256 B = fromBytes(A._bytes(), 4, 3);

        assertEq(A, B);

        B = fromBytes_(A._bytes(), 4, 3);
        // The header data should actually be equal now,
        // because we're referencing the same underlying data.
        assertEq(UM256.unwrap(A), UM256.unwrap(B));
    }

    function test_copy() public {
        UM256 A = fromArray(MATRIX_43);
        UM256 B = A.copy();

        assertEq(A, B);
        assertTrue(A.ref() != B.ref());
    }

    /* ------------- functions ------------- */

    function test_eq() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        UM256 B = A.copy();

        assertEq(A, B);

        A.set(0, 0, 9);
        assertFalse(A.eq(B));

        B.set(0, 0, 9);
        assertEq(A, B);
    }

    function test_sum() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);

        assertEq(A.sum(), 45);
    }

    function test_addScalarUnchecked() public {
        UM256 A = range(1, 10);

        assertEq(A.addScalarUnchecked(1), range(2, 11));
        assertEq(A.addScalarUnchecked(10), range(11, 20));
    }

    function test_mulScalarUnchecked() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        UM256 B = fromArray([[2, 4, 6], [8, 10, 12], [14, 16, 18]]);

        assertEq(A.mulScalarUnchecked(2), B);
    }

    function test_dot() public {
        UM256 A = fromArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
        UM256 B = fromArray([[5, 7, 8], [6, 7, 9], [6, 8, 9]]);
        UM256 C = fromArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

        assertEq(A.dot(B), C);
        assertNEq(B.dot(A), C);

        A = fromArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
        B = fromArray([[1, 0, 1, 0], [0, 2, 0, 2], [0, 0, 3, 0], [3, 0, 0, 4]]);
        C = fromArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

        assertEq(A.dot(B), C);
        assertNEq(B.dot(A), C);
    }

    function test_dotTransposed() public {
        UM256 A = fromArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
        UM256 B = fromArray([[5, 6, 6], [7, 7, 8], [8, 9, 9]]);
        UM256 C = fromArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

        assertEq(A.dotTransposed(B), C);
        assertNEq(B.dotTransposed(A), C);

        A = fromArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
        B = fromArray([[1, 0, 0, 3], [0, 2, 0, 0], [1, 0, 3, 0], [0, 2, 0, 4]]);
        C = fromArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

        assertEq(A.dotTransposed(B), C);
        assertNEq(B.dotTransposed(A), C);
    }

    function test_add() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        UM256 B = fromArray([[1, 1, 1], [2, 2, 2], [3, 3, 3]]);
        UM256 C = fromArray([[2, 3, 4], [6, 7, 8], [10, 11, 12]]);

        assertEq(A.add(B), C);
        assertEq(A.add(zeros(3, 3)), A);
    }

    function test_eqScalar() public {
        UM256 A = range(1, 10);

        assertFalse(A.eqScalar(0));
        assertTrue(A.mulScalarUnchecked(0).eqScalar(0));
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

    function test__perf_eye_128() public pure {
        eye(128, 128);
    }

    function test__perf_addScalarUnchecked_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.addScalarUnchecked(1);
    }

    function test__perf_mulScalarUnchecked_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.mulScalarUnchecked(1);
    }

    function test__perf_eqScalar_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.set(100, 100, 3);

        A.eqScalar(1);
    }

    function test__perf_add_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.add(B);
    }

    function test__perf_dot_16() public pure {
        UM256 A = mallocUM256(16, 16);
        UM256 B = mallocUM256(16, 16);

        A.dot(B);
    }

    function test__perf_dot_32() public pure {
        UM256 A = mallocUM256(32, 32);
        UM256 B = mallocUM256(32, 32);

        A.dot(B);
    }

    function test__perf_dot_64() public pure {
        UM256 A = mallocUM256(64, 64);
        UM256 B = mallocUM256(64, 64);

        A.dot(B);
    }

    function test__perf_dot_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.dot(B);
    }

    function test__perf_dotTransposed_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.dotTransposed(B);
    }

    function test__perf_sum_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.sum();
    }

    function test__perf_eq_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.eq(B);
    }

    function test__perf_fill_1024() public pure {
        UM256 A = mallocUM256(128, 128);

        A.fill_(1);
    }

    /* ------------- memory safety ------------- */

    modifier testMemorySafe(UM256 A) {
        memSafeTestMat = A;

        uint256 loc1 = freeMemPtr();
        // Skip magic valaue at `loc1`.
        // Skip matrix bytes length encoding.
        // Skip matrix data encoding.
        uint256 loc2 = loc1 + 32 + (1 + A.length()) * 32;

        storeMagicValueAt(loc1);
        storeMagicValueAt(loc2);

        // Set the free memory pointer to after the first magic value.
        setFreeMemPtr(loc1 + 32);

        _;

        // Make sure both magic values can be safely retrieved.
        bytes32 v1 = mload(loc1);
        bytes32 v2 = mload(loc2);

        assertEq(v1, _MAGIC_VALUE, "Magic Value not found");
        assertEq(v2, _MAGIC_VALUE, "Magic Value not found");
    }

    function test_addScalarUnchecked_memory_safe() public testMemorySafe(fromArray(MATRIX_43)) {
        memSafeTestMat.addScalarUnchecked(1);
    }

    function test_mulScalarUnchecked_memory_safe() public testMemorySafe(fromArray(MATRIX_43)) {
        memSafeTestMat.mulScalarUnchecked(1);
    }

    // function test_add_memory_safe() public testMemorySafe(fromArray(MATRIX_43)) {
    //     memSafeTestMat.add(1);
    // }
}
