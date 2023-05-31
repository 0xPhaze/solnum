// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import { N32x32, N32x32Lib } from "../src/N32x32.sol";
import { M32x32, M32x32Lib } from "../src/M32x32.sol";
import { Random, RandomLib } from "../src/Random.sol";
import "../src/utils/SolnumTestHelper.sol";

contract TestM32x32 is SolnumTestHelper {
    uint8[3][4] MATRIX_43 = [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]];

    /* ------------- header ------------- */

    function test_header(uint64 data, uint24 n, uint24 m) public {
        M32x32 A = M32x32Lib.M32x32Header(data, n, m);
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
        // uint256 size = n * m * 8;
        // uint256 msize = (size + 31) & 31;
        // expectSafeMemoryIncrease(msize + 32);

        M32x32 A = M32x32Lib.zeros(n, m);

        assertEq(A.ref(), memPtr + 32);

        (uint256 nA, uint256 mA, uint256 refA) = A.header();

        assertEq(A, 0);
        assertEq(nA, n);
        assertEq(mA, m);
        assertEq(refA, memPtr + 32);
    }

    function test_ones(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        M32x32 A = M32x32Lib.ones(n, m);

        assertEq(A, N32x32Lib.ONE);
    }

    function test_eye() public {
        M32x32 A = M32x32Lib.eye(3, 3);

        assertIsEye(A);
    }

    function test_full(uint256 n, uint256 m, N32x32 s) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        M32x32 A = M32x32Lib.full(n, m, s);

        assertEq(A, s);
    }

    function test_range(uint256 start, uint256 len) public {
        len = bound(len, 0, 50);
        start = bound(start, 0, 100_000);

        M32x32 A = M32x32Lib.range(start, start + len);

        for (uint256 i; i < len; i++) {
            assertEq(A.atIndex(i), N32x32Lib.fromUint(start + i));
        }
    }

    /* ------------- set ------------- */

    function test_setIndex(uint256 n, int64[20][2] calldata data) public {
        n = bound(n, 1, 20);

        M32x32 A = M32x32Lib.zeros(1, n);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);

        N32x32[20] memory B;

        // Store data at random positions.
        // Apply the same changes to `B`.
        for (uint256 k; k < data.length; k++) {
            uint256 i = uint64(data[k][0]) % n;
            N32x32 v = N32x32.wrap(data[k][1]);

            B[i] = v;

            A.setIndex(i, v);
        }

        // Make sure these values can be retrieved again.
        for (uint256 k; k < data.length; k++) {
            uint256 i = uint64(data[k][0]) % n;

            assertEq(A.atIndex(i), B[i]);
        }
    }

    function test_set(uint256 n, uint256 m, int64[10][3] calldata data) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        M32x32 A = M32x32Lib.zeros(n, m);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A); // todo: change to magic val

        N32x32[10][10] memory B;

        // Store data at random positions.
        // Apply the same changes to `B`.
        for (uint256 k; k < data.length; k++) {
            uint256 i = uint64(data[k][0]) % n;
            uint256 j = uint64(data[k][1]) % m;
            N32x32 v = N32x32.wrap(int64(data[k][2]));

            B[i][j] = v;

            A.set(i, j, v);
        }

        // Make sure these values can be retrieved again.
        for (uint256 k; k < data.length; k++) {
            uint256 i = uint64(data[k][0]) % n;
            uint256 j = uint64(data[k][1]) % m;

            assertEq(A.at(i, j), B[i][j]);
        }
    }

    /* ------------- Mat -> Scalar operators ------------- */

    function test_sum(uint256 n, uint256 m) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        uint256 len = n * m;

        M32x32 A = M32x32Lib.range(1, len + 1).reshape(n, m);

        assertEq(A.sum(), N32x32Lib.fromUint((len * (len + 1)) / 2));
        assertEq(A.neg().sum(), N32x32Lib.fromUint((len * (len + 1)) / 2).neg());
    }

    function test_sumEq(uint256 n, uint256 m, uint256 i) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);
        i = bound(i, 0, n * m - 1);

        uint256 len = n * m;

        M32x32 A = M32x32Lib.range(len).reshape(n, m);

        assertEq(A.sumEq(A), N32x32Lib.fromUint(len));

        M32x32 B = A.copy();

        B.setIndex(i, N32x32Lib.fromInt(-1));

        assertEq(A.sumEq(B), N32x32Lib.fromUint(len - 1));
    }

    function test_mean(uint256 n, uint256 m) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        uint256 len = n * m;

        M32x32 A = M32x32Lib.range(1, len + 1).reshape(n, m);

        assertEq(A.mean(), N32x32Lib.fromUint(len + 1).divInt(2));
        assertEq(A.neg().mean(), N32x32Lib.fromUint(len + 1).divInt(-2));
    }

    function test_vari() public {
        assertEq(M32x32Lib.range(2).vari(), N32x32Lib.HALF);
        assertEq(M32x32Lib.range(3).vari(), N32x32Lib.ONE);
        assertEq(M32x32Lib.range(7).vari(), N32x32Lib.fromWAD(4_666666666666666666));
        assertEq(M32x32Lib.range(100).vari(), N32x32Lib.fromWAD(841_666666666666666666));
    }

    function test_minMax(uint256 n, N32x32 a, uint256 i, uint256 j, N32x32 minValue, N32x32 maxValue) public {
        n = bound(n, 2, 20);
        i = bound(i, 0, n - 1);
        j = bound(j, i + 1, i + n - 1) % n;

        maxValue = bound(maxValue, N32x32Lib.MIN, N32x32Lib.MAX);
        minValue = bound(minValue, N32x32Lib.MIN, maxValue);

        M32x32 A = M32x32Lib.full(1, n, a);

        if (a.lt(minValue)) minValue = a;
        if (a.gt(maxValue)) maxValue = a;

        A.setIndex(i, minValue);
        A.setIndex(j, maxValue);

        (N32x32 minValue_, N32x32 maxValue_) = A.minMax();

        // logMat(A);

        assertEq(A.min(), minValue);
        assertEq(A.max(), maxValue);
        assertEq(minValue_, minValue);
        assertEq(maxValue_, maxValue);
    }

    /* ------------- Mat x Scalar -> Scalar operators ------------- */

    function test_eqAllScalar(uint256 n, uint256 i, N32x32 a, N32x32 s) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = M32x32Lib.full(1, n, a);

        appendMagicValue(A); // This value should not be touched.
        assertEq(A, a);

        A.set(0, i, s); // Set any entry to `s`.

        assertEq(A.eqAllScalar(a), a.eq(s)); // `A == a` holds iff `a == s`.
        assertMagicValueAt(A); // Make sure the magic value can be retrieved.
    }

    function test_ltAllScalar(uint256 n, uint256 i, N32x32 a, N32x32 b, N32x32 s) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = M32x32Lib.full(1, n, a);

        appendMagicValue(A); // This value should not be touched.
        assertEq(A.ltAllScalar(s), a.lt(s));

        A.set(0, i, b);

        N32x32 maxA = n == 1 ? b : N32x32Lib.max(a, b);

        assertEq(A.ltAllScalar(s), maxA.lt(s));
        assertMagicValueAt(A); // Make sure the magic value can be retrieved.
    }

    function test_lteAllScalar(uint256 n, uint256 i, N32x32 a, N32x32 b, N32x32 s) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = M32x32Lib.full(1, n, a);

        appendMagicValue(A); // This value should not be touched.
        assertEq(A.lteAllScalar(s), a.lte(s));

        A.set(0, i, b);

        N32x32 maxA = n == 1 ? b : N32x32Lib.max(a, b);

        assertEq(A.lteAllScalar(s), maxA.lte(s));
        assertMagicValueAt(A); // Make sure the magic value can be retrieved.
    }

    function test_gtAllScalar(uint256 n, uint256 i, N32x32 a, N32x32 b, N32x32 s) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = M32x32Lib.full(1, n, a);

        appendMagicValue(A); // This value should not be touched.
        assertEq(A.gtAllScalar(s), a.gt(s));

        A.set(0, i, b);

        N32x32 minA = n == 1 ? b : N32x32Lib.min(a, b);

        assertEq(A.gtAllScalar(s), minA.gt(s));
        assertMagicValueAt(A); // Make sure the magic value can be retrieved.
    }

    function test_gteAllScalar(uint256 n, uint256 i, N32x32 a, N32x32 b, N32x32 s) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = M32x32Lib.full(1, n, a);

        appendMagicValue(A); // This value should not be touched.
        assertEq(A.gteAllScalar(s), a.gte(s));

        A.set(0, i, b);

        N32x32 minA = n == 1 ? b : N32x32Lib.min(a, b);

        assertEq(A.gteAllScalar(s), minA.gte(s));
        assertMagicValueAt(A); // Make sure the magic value can be retrieved.
    }

    /* ------------- Mat x Mat -> Scalar operators ------------- */

    function test_eqAll(uint256 n, uint256 i) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        M32x32 A = M32x32Lib.range(1, n + 1);
        M32x32 B = M32x32Lib.range(1, n + 1);

        // Make sure out of bounds values are not used.
        appendDirtyBits(A);
        appendDirtyBits(B);

        assertEq(A, B);

        // Setting any entry to `0`, `A = B` does not hold.
        A.set(0, i, N32x32Lib.ZERO);
        assertNEq(A, B);
    }

    /* ------------- Mat -> Mat operators ------------- */

    function test_reshape() public {
        M32x32 A = M32x32Lib.range(1, 13);
        M32x32 B = M32x32Lib.range(1, 13);

        assertEq(A.reshape(4, 3), B.reshape(4, 3));
        assertNEq(A.reshape(3, 4), B.reshape(4, 3));

        (uint256 n, uint256 m) = B.reshape(4, 3).shape();

        assertEq(n, 4);
        assertEq(m, 3);
    }

    function test_transpose(uint256 n, uint256 m) public {
        log_mat_decimals = 0;
        log_mat_extended = false;
        log_mat_max = 15;

        n = bound(n, 1, 32);
        m = bound(m, 1, 32);

        M32x32 A = M32x32Lib.range(1, 1 + n * m).reshape(n, m);

        appendMagicValue(A);

        M32x32 A_T = A.T();

        // Note: should be pre-computed.
        assertMagicValueAt(A);

        assertEq(A_T.dim0(), m);
        assertEq(A_T.dim1(), n);

        assertEq(A_T.T(), A);
    }

    // function test_map() public {
    //     M32x32 A = M32x32Lib.fromUintArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
    //     M32x32 B = M32x32Lib.fromUintArray([[4, 7, 10], [13, 16, 19], [22, 25, 28]]);

    //     assertEq(A.map(affineMap), B);
    // }

    /* ------------- Mat x Scalar -> Mat operators ------------- */

    function test_addScalar(uint256 n, uint256 i, N32x32 a, N32x32 b) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        // Test on a full matrix.
        M32x32 A = M32x32Lib.full(1, n, a);

        (bool success, N32x32 c) = a.tryAdd(b);
        if (!success) vm.expectRevert(N32x32Lib.Overflow.selector);

        M32x32 C = A.addScalar(b);

        assertEq(C, c);

        // Test on a sparse matrix.
        A = M32x32Lib.zeros(1, n);
        A.set(0, i, a);

        C = A.addScalar(b);

        assertEq(c.gt(b) ? C.max() : C.min(), c);
    }

    function test_addScalarUnchecked(uint256 n, uint256 i, N32x32 a, N32x32 b) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        // Test on a full matrix.
        M32x32 A = M32x32Lib.full(1, n, a);

        assertEq(A.addScalarUnchecked(b), a.addUnchecked(b));

        // Test on a sparse matrix.
        A = M32x32Lib.zeros(1, n);
        A.set(0, i, a);

        N32x32 c = a.addUnchecked(b);
        M32x32 C = A.addScalarUnchecked(b);

        assertEq(c.gt(b) ? C.max() : C.min(), c);
    }

    function test_mulScalar(uint256 n, uint256 i, N32x32 a, N32x32 b) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        // Test on a full matrix.
        M32x32 A = M32x32Lib.full(1, n, a);

        (bool success, N32x32 c) = a.tryMul(b);
        if (!success) vm.expectRevert(N32x32Lib.Overflow.selector);

        assertEq(A.mulScalar(b), c);

        // Test on a sparse matrix.
        A = M32x32Lib.zeros(1, n);
        A.set(0, i, a);

        M32x32 C = A.mulScalar(b);

        assertEq(c.isPositive() ? C.max() : C.min(), c);
    }

    function test_mulScalarUnchecked(uint256 n, uint256 i, N32x32 a, N32x32 b) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        // Test on a full matrix.
        M32x32 A = M32x32Lib.full(1, n, a);

        assertEq(A.mulScalarUnchecked(b), a.mulUnchecked(b));

        // Test on a sparse matrix.
        A = M32x32Lib.zeros(1, n);
        A.set(0, i, a);

        N32x32 c = a.mulUnchecked(b);
        M32x32 C = A.mulScalarUnchecked(b);

        assertEq(c.isPositive() ? C.max() : C.min(), c);
    }

    function test_abs() public {
        M32x32 A = M32x32Lib.fromIntEncoded(abi.encode([[-1, 2, -3], [-1, 1, 1]]));
        M32x32 B = M32x32Lib.fromIntEncoded(abi.encode([[-1, 2, 3, 4], [-1, 1, 1, -4]]));
        M32x32 C = M32x32Lib.fromIntEncoded(abi.encode([[1, 2, 3, 4], [1, 1, 1, 4]]));
        C.set(0, 0, N32x32Lib.fromInt(type(int32).min));

        assertEq(A.abs(), M32x32Lib.fromIntEncoded(abi.encode([[1, 2, 3], [1, 1, 1]])));
        assertEq(B.abs(), M32x32Lib.fromIntEncoded(abi.encode([[1, 2, 3, 4], [1, 1, 1, 4]])));

        vm.expectRevert(N32x32Lib.Overflow.selector);

        C.abs();
    }

    function test_positive() public {
        M32x32 A = M32x32Lib.fromIntEncoded(abi.encode([[-1, 2, -3], [-1, 1, 1]]));
        M32x32 B = M32x32Lib.fromIntEncoded(abi.encode([[-1, 2, 3, 4], [-1, 1, 1, -4]]));
        M32x32 C = M32x32Lib.fromIntEncoded(abi.encode([[1, 2, 3, 4], [1, 1, 1, 4]]));

        C.set(0, 0, N32x32Lib.fromInt(type(int32).min));

        assertEq(A.positive(), M32x32Lib.fromIntEncoded(abi.encode([[0, 2, 0], [0, 1, 1]])));
        assertEq(B.positive(), M32x32Lib.fromIntEncoded(abi.encode([[0, 2, 3, 4], [0, 1, 1, 0]])));
    }

    function test_linearReluTransposed() public {
        Random r = RandomLib.seed(0);
        M32x32 A = M32x32Lib.zeros(6, 5);
        M32x32 B = r.randn(4, 5);
        M32x32 bias = r.randn(1, 4);

        assertEq(A.dotTransposed(B).addBroadcast(bias).positive(), A.linearReluTransposed(B, bias));
    }

    function test_fill(uint256 n, uint256 m, N32x32 s) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        M32x32 A = M32x32Lib.zeros(n, m);
        A.fill_(s);

        assertEq(A, s);
    }

    /* ------------- Mat x Mat -> Mat operators ------------- */

    // TODO add random tests: (a + a) = 2a
    function test_add() public {
        test_add(4, 3, N32x32Lib.ONE, N32x32Lib.MAX);
    }

    function test_add(uint256 n, uint256 i, N32x32 a, N32x32 b) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        (bool success, N32x32 c) = a.tryAdd(b);
        if (!success) vm.expectRevert(N32x32Lib.Overflow.selector);

        // Test on a sparse matrix.
        M32x32 A = M32x32Lib.zeros(1, n);
        M32x32 B = M32x32Lib.zeros(1, n);

        A.set(0, i, a);
        B.set(0, i, b);

        // logMat("A", A);
        // logMat("B", B);

        M32x32 C = A.add(B);

        // logMat("C", C);

        assertEq(c.isPositive() ? C.max() : C.min(), c);

        // Test on a full matrix.
        A = M32x32Lib.full(1, n, a);
        B = M32x32Lib.full(1, n, b);

        assertEq(A.add(B), c);
        // logMat("C", A.add(B));
    }

    function test_addBroadcast() public {
        // M32x32 A = M32x32Lib.fromUintEncoded(abi.encode([[1, 2, 3], [4, 5, 6], [7, 8, 9]])).reshape(3, 3);
        // M32x32 B = M32x32Lib.fromUintEncoded(abi.encode([1, 2, 3])).reshape(1, 3);
        // M32x32 C = M32x32Lib.fromUintEncoded(abi.encode([[2, 4, 6], [5, 7, 9], [8, 10, 12]])).reshape(3, 3);

        M32x32 A = M32x32Lib.fromUintEncoded(abi.encode([[1, 2, 3, 4], [4, 5, 6, 7], [7, 8, 9, 10]])).reshape(3, 4);
        M32x32 B = M32x32Lib.fromUintEncoded(abi.encode([1, 2, 3, 4])).reshape(1, 4);
        M32x32 C = M32x32Lib.fromUintEncoded(abi.encode([[2, 4, 6, 8], [5, 7, 9, 11], [8, 10, 12, 14]])).reshape(3, 4);

        // B = M32x32Lib.fromUintEncoded(abi.encode([1, 2, 3])).reshape(3, 1);
        // C = M32x32Lib.fromUintEncoded(abi.encode([[2, 3, 4, 5], [6, 7, 8, 9], [10, 11, 12, 13]])).reshape(3, 4);

        // logMat("A", A);
        // logMat("B", B);
        // logMat("C", C);

        assertEq(A.addBroadcast(B), C);
    }

    function test_addUnchecked(uint256 n, uint256 i, N32x32 a, N32x32 b) public {
        n = bound(n, 1, 20);
        i = bound(i, 0, n - 1);

        // Test on a full matrix.
        M32x32 A = M32x32Lib.full(1, n, a);
        M32x32 B = M32x32Lib.full(1, n, b);

        assertEq(A.addUnchecked(B), a.addUnchecked(b));

        // Test on a sparse matrix.
        A = M32x32Lib.zeros(1, n);
        B = M32x32Lib.zeros(1, n);
        A.set(0, i, a);
        B.set(0, i, b);

        N32x32 c = a.addUnchecked(b);
        M32x32 C = A.addUnchecked(B);

        // log_mat_extended = true;

        // logMat("A", A);
        // logMat("B", B);
        // logMat("C", C);

        assertEq(c.isPositive() ? C.max() : C.min(), c);
    }

    // todo: add dot test with magic value

    // function test_dot() public {
    //     M32x32 A;
    //     M32x32 B;
    //     M32x32 C;

    //     // A = M32x32Lib.fromUintArray([[1]]);
    //     // assertEq(A.dot(A), 1);

    //     // A = M32x32Lib.fromUintArray([[1, 2]]);
    //     // assertEq(A.dot(A), 1);

    //     A = M32x32Lib.range(1, 2);
    //     assertEq(A.dot(A.T()), 1);
    //     A = M32x32Lib.range(1, 3);
    //     assertEq(A.dot(A.T()), 5);
    //     A = M32x32Lib.range(1, 4);
    //     assertEq(A.dot(A.T()), 14);
    //     A = M32x32Lib.range(1, 5);
    //     assertEq(A.dot(A.T()), 30);
    //     A = M32x32Lib.range(1, 6);
    //     assertEq(A.dot(A.T()), 55);
    //     A = M32x32Lib.range(1, 7);
    //     assertEq(A.dot(A.T()), 91);
    //     A = M32x32Lib.range(1, 8);
    //     assertEq(A.dot(A.T()), 140);

    //     A = M32x32Lib.fromUintArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
    //     B = M32x32Lib.fromUintArray([[5, 7, 8], [6, 7, 9], [6, 8, 9]]);
    //     C = M32x32Lib.fromUintArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

    //     assertEq(A.dot(B), C);
    //     assertNEq(B.dot(A), C);

    //     A = M32x32Lib.fromUintArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
    //     B = M32x32Lib.fromUintArray([[1, 0, 1, 0], [0, 2, 0, 2], [0, 0, 3, 0], [3, 0, 0, 4]]);
    //     C = M32x32Lib.fromUintArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

    //     // M32x32 A = M32x32Lib.fromUintArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
    //     // M32x32 B = M32x32Lib.fromUintArray([[5, 6, 6], [7, 7, 8], [8, 9, 9]]);
    //     // M32x32 C = M32x32Lib.fromUintArray([[28, 31, 32], [55, 60, 63], [88, 97, 101]]);

    //     assertEq(A.dot(B), C);
    //     assertNEq(B.dot(A), C);
    // }

    function test_dotTransposed() public logs_gas {
        M32x32 A = M32x32Lib.fromUintArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
        M32x32 B = M32x32Lib.fromUintArray([[5, 6, 6], [7, 7, 8], [8, 9, 9]]);
        M32x32 C = M32x32Lib.fromUintArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

        // logMat("A", A);
        // logMat("B", B);
        // logMat("C", C);

        assertEq(A.dotTransposed(B), C);
        assertNEq(B.dotTransposed(A), C);

        A = M32x32Lib.fromUintArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
        B = M32x32Lib.fromUintArray([[1, 0, 0, 3], [0, 2, 0, 0], [1, 0, 3, 0], [0, 2, 0, 4]]);
        C = M32x32Lib.fromUintArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

        assertEq(A.dotTransposed(B), C);
        assertNEq(B.dotTransposed(A), C);

        A.set(0, 1, N32x32Lib.fromUint((1 << 31) - 1));

        vm.expectRevert(N32x32Lib.Overflow.selector);

        A.dotTransposed(B);
    }

    // function test_dot() public {
    //     M32x32 A = M32x32Lib.fromUintArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
    //     M32x32 B = M32x32Lib.fromUintArray([[5, 7, 8], [6, 7, 9], [6, 8, 9]]);
    //     M32x32 AB = M32x32Lib.fromUintArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

    //     assertEq(A.dot(B), AB);
    //     assertNEq(B.dot(A), AB);

    //     A = M32x32Lib.fromUintArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
    //     B = M32x32Lib.fromUintArray([[1, 0, 1, 0], [0, 2, 0, 2], [0, 0, 3, 0], [3, 0, 0, 4]]);
    //     AB = M32x32Lib.fromUintArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

    //     assertEq(A.dot(B), AB);
    //     assertNEq(B.dot(A), AB);

    //     // for m in range(1, 9):
    //     //     for n in range(1, m + 1):
    //     //         A = np.arange(1, 1 + n * m).reshape(n, m)
    //     //         B = np.arange(2, 2 + n * m).reshape(m, n)
    //     //         print(repr(A.dot(B).flatten()))

    //     M32x32[] memory C = new M32x32[](36);

    //     C[0] = M32x32Lib.fromAbiEncoded(abi.encode([2]));//forgefmt: disable-line
    //     C[1] = M32x32Lib.fromAbiEncoded(abi.encode([8]));//forgefmt: disable-line
    //     C[2] = M32x32Lib.fromAbiEncoded(abi.encode([10, 13, 22, 29]));//forgefmt: disable-line
    //     C[3] = M32x32Lib.fromAbiEncoded(abi.encode([20]));//forgefmt: disable-line
    //     C[4] = M32x32Lib.fromAbiEncoded(abi.encode([28, 34, 64, 79]));//forgefmt: disable-line
    //     C[5] = M32x32Lib.fromAbiEncoded(abi.encode([ 36,  42,  48,  81,  96, 111, 126, 150, 174]));//forgefmt: disable-line
    //     C[6] = M32x32Lib.fromAbiEncoded(abi.encode([40]));//forgefmt: disable-line
    //     C[7] = M32x32Lib.fromAbiEncoded(abi.encode([ 60,  70, 140, 166]));//forgefmt: disable-line
    //     C[8] = M32x32Lib.fromAbiEncoded(abi.encode([ 80,  90, 100, 184, 210, 236, 288, 330, 372]));//forgefmt: disable-line
    //     C[9] = M32x32Lib.fromAbiEncoded(abi.encode([100, 110, 120, 130, 228, 254, 280, 306, 356, 398, 440, 482, 484, 542, 600,
    // 658]));//forgefmt: disable-line
    //     C[10] = M32x32Lib.fromAbiEncoded(abi.encode([70]));//forgefmt: disable-line
    //     C[11] = M32x32Lib.fromAbiEncoded(abi.encode([110, 125, 260, 300]));//forgefmt: disable-line
    //     C[12] = M32x32Lib.fromAbiEncoded(abi.encode([150, 165, 180, 350, 390, 430, 550, 615, 680]));//forgefmt: disable-line
    //     C[13] = M32x32Lib.fromAbiEncoded(abi.encode([ 190,  205,  220,  235,  440,  480,  520,  560,  690,  755,  820, 885,  940,
    // 1030, 1120, 1210]));//forgefmt: disable-line
    //     C[14] = M32x32Lib.fromAbiEncoded(abi.encode([ 230,  245,  260,  275,  290,  530,  570,  610,  650,  690,  830, 895,  960,
    // 1025, 1090, 1130, 1220, 1310, 1400, 1490, 1430, 1545, 1660, 1775, 1890]));//forgefmt: disable-line
    //     C[15] = M32x32Lib.fromAbiEncoded(abi.encode([112]));//forgefmt: disable-line
    //     C[16] = M32x32Lib.fromAbiEncoded(abi.encode([182, 203, 434, 491]));//forgefmt: disable-line
    //     C[17] = M32x32Lib.fromAbiEncoded(abi.encode([ 252,  273,  294,  594,  651,  708,  936, 1029, 1122]));//forgefmt:
    // disable-line
    //     C[18] = M32x32Lib.fromAbiEncoded(abi.encode([ 322,  343,  364,  385,  754,  811,  868,  925, 1186, 1279, 1372, 1465,
    // 1618, 1747, 1876, 2005]));//forgefmt: disable-line
    //     C[19] = M32x32Lib.fromAbiEncoded(abi.encode([ 392,  413,  434,  455,  476,  914,  971, 1028, 1085, 1142, 1436, 1529,
    // 1622, 1715, 1808, 1958, 2087, 2216, 2345, 2474, 2480, 2645, 2810, 2975, 3140]));//forgefmt: disable-line
    //     C[20] = M32x32Lib.fromAbiEncoded(abi.encode([ 462,  483,  504,  525,  546,  567, 1074, 1131, 1188, 1245, 1302, 1359,
    // 1686, 1779, 1872, 1965, 2058, 2151, 2298, 2427, 2556, 2685, 2814, 2943, 2910, 3075, 3240, 3405, 3570, 3735, 3522,
    // 3723, 3924, 4125, 4326, 4527]));//forgefmt: disable-line
    //     C[21] = M32x32Lib.fromAbiEncoded(abi.encode([168]));//forgefmt: disable-line
    //     C[22] = M32x32Lib.fromAbiEncoded(abi.encode([280, 308, 672, 749]));//forgefmt: disable-line
    //     C[23] = M32x32Lib.fromAbiEncoded(abi.encode([ 392,  420,  448,  931, 1008, 1085, 1470, 1596, 1722]));//forgefmt:
    // disable-line
    //     C[24] = M32x32Lib.fromAbiEncoded(abi.encode([ 504,  532,  560,  588, 1190, 1267, 1344, 1421, 1876, 2002, 2128, 2254,
    // 2562, 2737, 2912, 3087]));//forgefmt: disable-line
    //     C[25] = M32x32Lib.fromAbiEncoded(abi.encode([ 616,  644,  672,  700,  728, 1449, 1526, 1603, 1680, 1757, 2282, 2408,
    // 2534, 2660, 2786, 3115, 3290, 3465, 3640, 3815, 3948, 4172, 4396, 4620, 4844]));//forgefmt: disable-line
    //     C[26] = M32x32Lib.fromAbiEncoded(abi.encode([ 728,  756,  784,  812,  840,  868, 1708, 1785, 1862, 1939, 2016, 2093,
    // 2688, 2814, 2940, 3066, 3192, 3318, 3668, 3843, 4018, 4193, 4368, 4543, 4648, 4872, 5096, 5320, 5544, 5768, 5628,
    // 5901, 6174, 6447, 6720, 6993]));//forgefmt: disable-line
    //     C[27] = M32x32Lib.fromAbiEncoded(abi.encode([ 840,  868,  896,  924,  952,  980, 1008, 1967, 2044, 2121, 2198, 2275,
    // 2352, 2429, 3094, 3220, 3346, 3472, 3598, 3724, 3850, 4221, 4396, 4571, 4746, 4921, 5096, 5271, 5348, 5572, 5796,
    // 6020, 6244, 6468, 6692, 6475, 6748, 7021, 7294, 7567, 7840, 8113, 7602, 7924, 8246, 8568, 8890, 9212,
    // 9534]));//forgefmt: disable-line
    //     C[28] = M32x32Lib.fromAbiEncoded(abi.encode([240]));//forgefmt: disable-line
    //     C[29] = M32x32Lib.fromAbiEncoded(abi.encode([ 408,  444,  984, 1084]));//forgefmt: disable-line
    //     C[30] = M32x32Lib.fromAbiEncoded(abi.encode([ 576,  612,  648, 1376, 1476, 1576, 2176, 2340, 2504]));//forgefmt:
    // disable-line
    //     C[31] = M32x32Lib.fromAbiEncoded(abi.encode([ 744,  780,  816,  852, 1768, 1868, 1968, 2068, 2792, 2956, 3120, 3284,
    // 3816, 4044, 4272, 4500]));//forgefmt: disable-line
    //     C[32] = M32x32Lib.fromAbiEncoded(abi.encode([ 912,  948,  984, 1020, 1056, 2160, 2260, 2360, 2460, 2560, 3408, 3572,
    // 3736, 3900, 4064, 4656, 4884, 5112, 5340, 5568, 5904, 6196, 6488, 6780, 7072]));//forgefmt: disable-line
    //     C[33] = M32x32Lib.fromAbiEncoded(abi.encode([ 1080,  1116,  1152,  1188,  1224,  1260,  2552,  2652,  2752, 2852,  2952,  3052,  4024,  4188,  4352,  4516,  4680,  4844,
    // 5496,  5724,  5952,  6180,  6408,  6636,  6968,  7260,  7552, 7844,  8136,  8428,  8440,  8796,  9152,  9508,  9864,
    // 10220]));//forgefmt: disable-line
    //     C[34] = M32x32Lib.fromAbiEncoded(abi.encode([ 1248,  1284,  1320,  1356,  1392,  1428,  1464,  2944,  3044, 3144,  3244,  3344,  3444,  3544,  4640,  4804,  4968,  5132,
    // 5296,  5460,  5624,  6336,  6564,  6792,  7020,  7248,  7476, 7704,  8032,  8324,  8616,  8908,  9200,  9492,  9784,  9728,
    // 10084, 10440, 10796, 11152, 11508, 11864, 11424, 11844, 12264, 12684, 13104, 13524, 13944]));//forgefmt:
    // disable-line
    //     C[35] = M32x32Lib.fromAbiEncoded(abi.encode([ 1416,  1452,  1488,  1524,  1560,  1596,  1632,  1668,  3336, 3436,  3536,  3636,  3736,  3836,  3936,  4036,  5256,  5420,
    // 5584,  5748,  5912,  6076,  6240,  6404,  7176,  7404,  7632, 7860,  8088,  8316,  8544,  8772,  9096,  9388,  9680,  9972,
    // 10264, 10556, 10848, 11140, 11016, 11372, 11728, 12084, 12440, 12796, 13152, 13508, 12936, 13356, 13776, 14196,
    // 14616, 15036, 15456, 15876, 14856, 15340, 15824, 16308, 16792, 17276, 17760, 18244]));//forgefmt: disable-line

    //     uint256 k;

    //     for (uint256 m = 1; m < 9; m++) {
    //         for (uint256 n = 1; n < m + 1; n++) {
    //             A = M32x32Lib.range(1, 1 + n * m).reshape(n, m);
    //             B = M32x32Lib.range(2, 2 + n * m).reshape(m, n);

    //             assertEq(A.dot(B), C[k++].reshape(n, n));
    //         }
    //     }
    // }

    /* ------------- conversions ------------- */

    function test_fromUintArray(uint256 n, uint256 m) public {
        n = bound(n, 1, 3);
        m = bound(m, 1, 10);

        uint256[][] memory array = rangeUintArray(0, n, m);

        M32x32 A = M32x32Lib.fromUintArray(array);

        for (uint256 i; i < n * m; i++) {
            assertEq(A.at(i / m, i % m), N32x32Lib.fromUint(array[i / m][i % m]));
        }
    }

    function test_fromUintArray_revert_Overflow(uint256 n, uint256 m, uint256 i, uint256 a) public {
        n = bound(n, 1, 3);
        m = bound(m, 1, 10);
        i = bound(i, 0, n * m - 1);

        uint256[][] memory array = rangeUintArray(0, n, m);
        array[i / m][i % m] = a;

        if (a > uint32(type(int32).max)) {
            vm.expectRevert(N32x32Lib.Overflow.selector);
        }

        M32x32Lib.fromUintArray(array);
    }

    function test_fromIntArray(uint256 n, uint256 m) public {
        n = bound(n, 1, 3);
        m = bound(m, 1, 10);

        int256[][] memory array = rangeIntArray(0, n, m);

        M32x32 A = M32x32Lib.fromIntArray(array);

        for (uint256 i; i < n * m; i++) {
            assertEq(A.at(i / m, i % m).toInt(), array[i / m][i % m]);
        }
    }

    function test_fromIntArray_revert_Overflow(uint256 n, uint256 m, uint256 i, int256 a) public {
        n = bound(n, 1, 3);
        m = bound(m, 1, 10);
        i = bound(i, 0, n * m - 1);

        int256[][] memory array = rangeIntArray(0, n, m);
        array[i / m][i % m] = a;

        if (a < type(int32).min || a > type(int32).max) {
            vm.expectRevert(N32x32Lib.Overflow.selector);
        }

        M32x32Lib.fromIntArray(array);
    }

    function test_fromUintEncoded() public {
        M32x32 A = M32x32Lib.fromUintEncoded(abi.encode([[1, 2, 3, 4], [5, 6, 7, 8]]));
        M32x32 B = M32x32Lib.fromUintEncoded(abi.encode([[1, 2, 3], [4, 5, 6], [7, 8, 9]]));

        assertEq(A, M32x32Lib.range(1, 9));
        assertEq(B, M32x32Lib.range(1, 10));
    }

    uint256 constant _n = 5;
    uint256 constant _m = 7;

    function test_fromUintEncoded(uint32[_m][_n] memory data) public {
        for (uint256 i; i < _n * _m; i++) {
            data[i / _m][i % _m] = uint32(bound(data[i / _m][i % _m], 0, uint256(N32x32Lib.INT32_MAX)));
        }

        M32x32 A = M32x32Lib.fromUintEncoded(abi.encode(data));

        for (uint256 i; i < _n * _m; i++) {
            assertEq(A.atIndex(i).toUint(), data[i / _m][i % _m]);
        }
    }

    function test_fromUintEncoded_revert_Overflow(uint64[_m][_n] memory data) public {
        for (uint256 i; i < _n * _m; i++) {
            if (data[i / _m][i % _m] > uint32(type(int32).max)) {
                vm.expectRevert(N32x32Lib.Overflow.selector);
                break;
            }
        }

        M32x32Lib.fromUintEncoded(abi.encode(data));
    }

    function test_fromIntEncoded() public {
        M32x32 A = M32x32Lib.fromIntEncoded(abi.encode([[1, 2, 3, 4], [5, 6, 7, 8]]));
        M32x32 B = M32x32Lib.fromIntEncoded(abi.encode([[1, 2, 3], [4, 5, 6], [7, 8, 9]]));

        assertEq(A, M32x32Lib.range(1, 9));
        assertEq(B, M32x32Lib.range(1, 10));
    }

    function test_fromIntEncoded(int32[_m][_n] memory data) public {
        for (uint256 i; i < _n * _m; i++) {
            data[i / _m][i % _m] = int32(int256(bound(uint32(data[i / _m][i % _m]), 0, uint256(N32x32Lib.UINT32_MAX))));
        }

        M32x32 A = M32x32Lib.fromIntEncoded(abi.encode(data));

        for (uint256 i; i < _n * _m; i++) {
            assertEq(A.atIndex(i).toInt(), data[i / _m][i % _m]);
        }
    }

    function test_fromIntEncoded_revert_Overflow(int256[_m][_n] memory data) public {
        for (uint256 i; i < _n * _m; i++) {
            int256 a = data[i / _m][i % _m];
            if (a < type(int32).min || a > type(int32).max) {
                vm.expectRevert(N32x32Lib.Overflow.selector);
                break;
            }
        }

        M32x32Lib.fromIntEncoded(abi.encode(data));
    }
}

// contract TestGasM32x32 {
//     /* ------------- constructors ------------- */

//     function test_perf_zeros_128() public pure {
//         zeros(128, 128);
//     }

//     function test_perf_ones_128() public pure {
//         ones(128, 128);
//     }

//     function test_perf_eye_128() public pure {
//         M32x32Lib.eye(128, 128);
//     }

//     function test_perf_full_128() public pure {
//         full(128, 128, ONE);
//     }

//     function test_perf_range_1024() public pure {
//         range(1024);
//     }

//     /* ------------- Mat -> Scalar operators ------------- */

//     function test_perf_sum_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.sum();
//     }

//     function test_perf_mean_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.mean();
//     }

//     function test_perf_min_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.min();
//     }

//     function test_perf_max_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.max();
//     }

//     function test_perf_minMax_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.minMax();
//     }

//     /* ------------- Mat x Scalar -> Scalar operators ------------- */

//     function test_perf_eqAllScalar_128() public pure {
//         M32x32 A = M32x32Lib.zeros(128, 128);

//         A.eqAllScalar(ZERO);
//         A.set(100, 100, ONE);
//         A.eqAllScalar(ZERO);
//     }

//     function test_perf_ltAllScalar_128() public pure {
//         M32x32 A = M32x32Lib.zeros(128, 128);

//         A.ltAllScalar(MAX);
//         A.set(100, 100, ONE);
//         A.ltAllScalar(MAX);
//     }

//     // function test_perf_gtAllScalar_128() public pure {
//     //     M32x32 A = ones(128, 128);

//     //     A.gtAllScalar(3);
//     //     A.set(100, 100, ZERO);
//     //     A.gtAllScalar(3);
//     // }

//     /* ------------- Mat x Mat -> Scalar operators ------------- */

//     function test_perf_eqAll_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);
//         M32x32 B = mallocM32x32(128, 128);

//         A.eqAll(B);
//     }

//     /* ------------- Mat -> Mat operators ------------- */

//     function test_perf_transpose_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.transpose();
//     }

//     function test_perf_transposeNaive_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.transposeNaive();
//     }

//     // function test_perf_map_128() public {
//     //     M32x32 A = mallocM32x32(128, 128);

//     //     A.map(affineMap);
//     // }

//     /* ------------- Mat x Scalar -> Mat operators ------------- */

//     function test_perf_addScalarUnchecked_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.addScalarUnchecked(1);
//     }

//     function test_perf_mulScalarUnchecked_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.mulScalarUnchecked(1);
//     }

//     function test_perf_addScalar_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.addScalar(1);
//     }

//     function test_perf_mulScalar_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.mulScalar(1);
//     }

//     function test_perf_fill_1024() public pure {
//         M32x32 A = mallocM32x32(128, 128);

//         A.fill_(N32x32.wrap(int64(int256(1))));
//     }

//     /* ------------- Mat x Mat -> Mat operators ------------- */

//     function test_perf_add_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);
//         M32x32 B = mallocM32x32(128, 128);

//         A.add(B);
//     }

//     function test_perf_addUnchecked_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);
//         M32x32 B = mallocM32x32(128, 128);

//         A.addUnchecked(B);
//     }

//     function test_perf_dot_16() public pure {
//         M32x32 A = mallocM32x32(16, 16);
//         M32x32 B = mallocM32x32(16, 16);

//         A.dot(B);
//     }

//     function test_perf_dot_32() public pure {
//         M32x32 A = mallocM32x32(32, 32);
//         M32x32 B = mallocM32x32(32, 32);

//         A.dot(B);
//     }

//     function test_perf_dot_64() public pure {
//         M32x32 A = mallocM32x32(64, 64);
//         M32x32 B = mallocM32x32(64, 64);

//         A.dot(B);
//     }

//     function test_perf_dot_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);
//         M32x32 B = mallocM32x32(128, 128);

//         A.dot(B);
//     }

//     function test_perf_dotTransposed_128() public pure {
//         M32x32 A = mallocM32x32(128, 128);
//         M32x32 B = mallocM32x32(128, 128);

//         A.dotTransposed(B);
//     }

//     /* ------------- utils ------------- */

//     function affineMap(uint256 a) internal pure returns (uint256) {
//         return a * 3 + 1;
//     }
// }

// contract TestMemSafe is SolnumTestHelper {
//     function test_magicValueTest(uint256 n) public {
//         n = bound(n, 1, 10);

//         M32x32 A = M32x32Lib.range(n);

//         appendMagicValue(A);
//         assertMagicValueAt(A);

//         uint256 lenUp = (n + 3) & ~uint256(3);

//         A.setUnsafe(0, lenUp, N32x32.wrap(int64(1)));
//     }

//     function testFail_magicValueTest(uint256 n) public {
//         n = bound(n, 1, 10);

//         M32x32 A = M32x32Lib.range(n);

//         appendMagicValue(A);
//         assertMagicValueAt(A);

//         uint256 lenUp = (n + 3) & ~uint256(3);

//         A.setUnsafe(0, lenUp, N32x32.wrap(int64(1)));
//         assertMagicValueAt(A);
//     }
// }
