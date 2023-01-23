// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/UM256.sol";
import "./utils/TestHelper.sol";

contract TestUM256 is TestHelper {
    uint8[3][4] MATRIX_43 = [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12]];

    /* ------------- malloc ------------- */

    // todo change to mallocUM256 test
    function test_malloc(uint256 sz) public {
        sz = bound(sz, 0, 50);

        uint256 memPtr = freeMemPtr();
        uint256 size = sz * 32;
        uint256 ptr = malloc(size);

        assertEq(freeMemPtr() - memPtr, size);
        assertEq(ptr, memPtr);
    }

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

    function test_ones(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        UM256 A = ones(n, m);

        assertEq(A, 1);
    }

    function test_eye() public {
        UM256 A = eye(3, 3);

        assertIsEye(A);
    }

    function test_full(uint256 n, uint256 m, uint256 s) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        UM256 A = full(n, m, s);

        assertEq(A, s);
    }

    function test_range(uint256 start, uint256 len) public {
        len = bound(len, 0, 50);
        start = bound(start, 0, 100_000);

        UM256 A = range(start, start + len);

        for (uint256 i; i < len; i++) {
            assertEq(A.atIndex(i), start + i);
        }
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

    /* ------------- Mat -> Scalar operators ------------- */

    function test_sum() public {
        UM256 A = range(10);

        assertEq(A.sum(), 45);
    }

    function test_mean() public {
        UM256 A = range(1, 10);

        assertEq(A.mean(), 5);
    }

    function test_vari() public {
        assertEq(range(2).vari(), 0); // note: 0.5 should be rounding up
        assertEq(range(3).vari(), 1);
        assertEq(range(7).vari(), 5);
        assertEq(range(100).vari(), 842); // Using unbiased estimator.
    }

    function test_minMax(uint256 n, uint256 s, uint256 i, uint256 j, uint256 minValue, uint256 maxValue) public {
        n = bound(n, 2, 20);
        i = bound(i, 0, n - 1);
        j = bound(j, i + 1, i + n - 1) % n;
        maxValue = bound(maxValue, 0, type(uint256).max);
        minValue = bound(minValue, 0, maxValue);

        UM256 A = full(1, n, s);

        if (s < minValue) minValue = s;
        if (s > maxValue) maxValue = s;

        A.setIndex(i, minValue);
        A.setIndex(j, maxValue);

        (uint256 minValue_, uint256 maxValue_) = A.minMax();

        assertEq(A.min(), minValue);
        assertEq(A.max(), maxValue);
        assertEq(minValue, minValue_);
        assertEq(maxValue, maxValue_);
    }

    /* ------------- Mat x Scalar -> Scalar operators ------------- */

    function test_eqAllScalar() public {
        UM256 A = range(1, 10);

        assertFalse(A.eqAllScalar(0));
        assertTrue(A.mulScalarUnchecked(0).eqAllScalar(0));
    }

    function test_ltAllScalar() public {
        UM256 A = range(1, 10);

        assertTrue(A.ltAllScalar(10));
        assertFalse(A.ltAllScalar(9));
        assertFalse(A.ltAllScalar(1));
        assertFalse(A.ltAllScalar(0));
    }

    function test_lteAllScalar() public {
        UM256 A = range(1, 10);

        assertTrue(A.lteAllScalar(9));
        assertFalse(A.lteAllScalar(8));
        assertFalse(A.lteAllScalar(0));
    }

    function test_gtAllScalar() public {
        UM256 A = range(1, 10);

        assertTrue(A.gtAllScalar(0));
        assertFalse(A.gtAllScalar(1));
        assertFalse(A.gtAllScalar(10));
    }

    function test_gteAllScalar() public {
        UM256 A = range(1, 10);

        assertTrue(A.gteAllScalar(0));
        assertTrue(A.gteAllScalar(1));
        assertFalse(A.gteAllScalar(2));
        assertFalse(A.gteAllScalar(9));
    }

    /* ------------- Mat x Mat -> Scalar operators ------------- */

    function test_eqAll() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        UM256 B = A.copy();

        assertEq(A, B);

        A.set(0, 0, 9);
        assertFalse(A.eqAll(B));

        B.set(0, 0, 9);
        assertEq(A, B);
    }

    /* ------------- Mat -> Mat operators ------------- */

    function test_reshape() public {
        UM256 A = range(1, 13);
        UM256 B = range(1, 13).reshape(4, 3);

        assertEq(A.reshape(4, 3), B);
        assertNEq(A.reshape(3, 4), B);

        (uint256 n, uint256 m) = B.shape();

        assertEq(n, 4);
        assertEq(m, 3);
    }

    function test_transpose(uint256 n, uint256 m) public {
        n = bound(n, 1, 4);
        m = bound(m, 1, 4);

        UM256 A = range(1, 1 + n * m).reshape(n, m);
        UM256 A_T = A.T();

        assertEq(A_T.dim0(), m);
        assertEq(A_T.dim1(), n);
        assertEq(A_T.T(), A);

        if (n == 1 && m == 1) {
            assertEq(A_T, A);
        } else {
            assertNEq(A_T, A);
        }
    }

    function test_map() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        UM256 B = fromArray([[4, 7, 10], [13, 16, 19], [22, 25, 28]]);

        assertEq(A.map(affineMap), B);
    }

    /* ------------- Mat x Scalar -> Mat operators ------------- */

    // todo: addScalar

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

    function test_fill(uint256 n, uint256 m) public {
        n = bound(n, 0, 10);
        m = bound(m, 0, 10);

        UM256 A = zeros(n, m);
        A.fill_(123);

        assertEq(A, 123);
    }

    /* ------------- Mat x Mat -> Mat operators ------------- */

    function test_add() public {
        UM256 A = fromArray([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);
        UM256 B = fromArray([[1, 1, 1], [2, 2, 2], [3, 3, 3]]);
        UM256 C = fromArray([[2, 3, 4], [6, 7, 8], [10, 11, 12]]);

        assertEq(A.add(B), C);
        assertEq(A.add(zeros(3, 3)), A);
    }

    function test_dot() public {
        // for m in range(1, 9):
        //     for n in range(1, m + 1):
        //         A = np.arange(1, 1 + n * m).reshape(n, m)
        //         B = np.arange(2, 2 + n * m).reshape(m, n)
        //         print(repr(A.dot(B).flatten()))

        UM256 A = fromArray([[1, 1, 2], [2, 3, 3], [4, 4, 5]]);
        UM256 B = fromArray([[5, 7, 8], [6, 7, 9], [6, 8, 9]]);
        UM256 AB = fromArray([[23, 30, 35], [46, 59, 70], [74, 96, 113]]);

        assertEq(A.dot(B), AB);
        assertNEq(B.dot(A), AB);

        A = fromArray([[1, 1, 0, 0], [0, 2, 2, 0], [0, 0, 3, 3], [4, 0, 4, 0]]);
        B = fromArray([[1, 0, 1, 0], [0, 2, 0, 2], [0, 0, 3, 0], [3, 0, 0, 4]]);
        AB = fromArray([[1, 2, 1, 2], [0, 4, 6, 4], [9, 0, 9, 12], [4, 0, 16, 0]]);

        assertEq(A.dot(B), AB);
        assertNEq(B.dot(A), AB);

        UM256[] memory C = new UM256[](36);

        C[0] = fromAbiEncoded(abi.encode([2]));//forgefmt: disable-line
        C[1] = fromAbiEncoded(abi.encode([8]));//forgefmt: disable-line
        C[2] = fromAbiEncoded(abi.encode([10, 13, 22, 29]));//forgefmt: disable-line
        C[3] = fromAbiEncoded(abi.encode([20]));//forgefmt: disable-line
        C[4] = fromAbiEncoded(abi.encode([28, 34, 64, 79]));//forgefmt: disable-line
        C[5] = fromAbiEncoded(abi.encode([ 36,  42,  48,  81,  96, 111, 126, 150, 174]));//forgefmt: disable-line
        C[6] = fromAbiEncoded(abi.encode([40]));//forgefmt: disable-line
        C[7] = fromAbiEncoded(abi.encode([ 60,  70, 140, 166]));//forgefmt: disable-line
        C[8] = fromAbiEncoded(abi.encode([ 80,  90, 100, 184, 210, 236, 288, 330, 372]));//forgefmt: disable-line
        C[9] = fromAbiEncoded(abi.encode([100, 110, 120, 130, 228, 254, 280, 306, 356, 398, 440, 482, 484, 542, 600, 658]));//forgefmt: disable-line
        C[10] = fromAbiEncoded(abi.encode([70]));//forgefmt: disable-line
        C[11] = fromAbiEncoded(abi.encode([110, 125, 260, 300]));//forgefmt: disable-line
        C[12] = fromAbiEncoded(abi.encode([150, 165, 180, 350, 390, 430, 550, 615, 680]));//forgefmt: disable-line
        C[13] = fromAbiEncoded(abi.encode([ 190,  205,  220,  235,  440,  480,  520,  560,  690,  755,  820, 885,  940, 1030, 1120, 1210]));//forgefmt: disable-line
        C[14] = fromAbiEncoded(abi.encode([ 230,  245,  260,  275,  290,  530,  570,  610,  650,  690,  830, 895,  960, 1025, 1090, 1130, 1220, 1310, 1400, 1490, 1430, 1545, 1660, 1775, 1890]));//forgefmt: disable-line
        C[15] = fromAbiEncoded(abi.encode([112]));//forgefmt: disable-line
        C[16] = fromAbiEncoded(abi.encode([182, 203, 434, 491]));//forgefmt: disable-line
        C[17] = fromAbiEncoded(abi.encode([ 252,  273,  294,  594,  651,  708,  936, 1029, 1122]));//forgefmt: disable-line
        C[18] = fromAbiEncoded(abi.encode([ 322,  343,  364,  385,  754,  811,  868,  925, 1186, 1279, 1372, 1465, 1618, 1747, 1876, 2005]));//forgefmt: disable-line
        C[19] = fromAbiEncoded(abi.encode([ 392,  413,  434,  455,  476,  914,  971, 1028, 1085, 1142, 1436, 1529, 1622, 1715, 1808, 1958, 2087, 2216, 2345, 2474, 2480, 2645, 2810, 2975, 3140]));//forgefmt: disable-line
        C[20] = fromAbiEncoded(abi.encode([ 462,  483,  504,  525,  546,  567, 1074, 1131, 1188, 1245, 1302, 1359, 1686, 1779, 1872, 1965, 2058, 2151, 2298, 2427, 2556, 2685, 2814, 2943, 2910, 3075, 3240, 3405, 3570, 3735, 3522, 3723, 3924, 4125, 4326, 4527]));//forgefmt: disable-line
        C[21] = fromAbiEncoded(abi.encode([168]));//forgefmt: disable-line
        C[22] = fromAbiEncoded(abi.encode([280, 308, 672, 749]));//forgefmt: disable-line
        C[23] = fromAbiEncoded(abi.encode([ 392,  420,  448,  931, 1008, 1085, 1470, 1596, 1722]));//forgefmt: disable-line
        C[24] = fromAbiEncoded(abi.encode([ 504,  532,  560,  588, 1190, 1267, 1344, 1421, 1876, 2002, 2128, 2254, 2562, 2737, 2912, 3087]));//forgefmt: disable-line
        C[25] = fromAbiEncoded(abi.encode([ 616,  644,  672,  700,  728, 1449, 1526, 1603, 1680, 1757, 2282, 2408, 2534, 2660, 2786, 3115, 3290, 3465, 3640, 3815, 3948, 4172, 4396, 4620, 4844]));//forgefmt: disable-line
        C[26] = fromAbiEncoded(abi.encode([ 728,  756,  784,  812,  840,  868, 1708, 1785, 1862, 1939, 2016, 2093, 2688, 2814, 2940, 3066, 3192, 3318, 3668, 3843, 4018, 4193, 4368, 4543, 4648, 4872, 5096, 5320, 5544, 5768, 5628, 5901, 6174, 6447, 6720, 6993]));//forgefmt: disable-line
        C[27] = fromAbiEncoded(abi.encode([ 840,  868,  896,  924,  952,  980, 1008, 1967, 2044, 2121, 2198, 2275, 2352, 2429, 3094, 3220, 3346, 3472, 3598, 3724, 3850, 4221, 4396, 4571, 4746, 4921, 5096, 5271, 5348, 5572, 5796, 6020, 6244, 6468, 6692, 6475, 6748, 7021, 7294, 7567, 7840, 8113, 7602, 7924, 8246, 8568, 8890, 9212, 9534]));//forgefmt: disable-line
        C[28] = fromAbiEncoded(abi.encode([240]));//forgefmt: disable-line
        C[29] = fromAbiEncoded(abi.encode([ 408,  444,  984, 1084]));//forgefmt: disable-line
        C[30] = fromAbiEncoded(abi.encode([ 576,  612,  648, 1376, 1476, 1576, 2176, 2340, 2504]));//forgefmt: disable-line
        C[31] = fromAbiEncoded(abi.encode([ 744,  780,  816,  852, 1768, 1868, 1968, 2068, 2792, 2956, 3120, 3284, 3816, 4044, 4272, 4500]));//forgefmt: disable-line
        C[32] = fromAbiEncoded(abi.encode([ 912,  948,  984, 1020, 1056, 2160, 2260, 2360, 2460, 2560, 3408, 3572, 3736, 3900, 4064, 4656, 4884, 5112, 5340, 5568, 5904, 6196, 6488, 6780, 7072]));//forgefmt: disable-line
        C[33] = fromAbiEncoded(abi.encode([ 1080,  1116,  1152,  1188,  1224,  1260,  2552,  2652,  2752, 2852,  2952,  3052,  4024,  4188,  4352,  4516,  4680,  4844, 5496,  5724,  5952,  6180,  6408,  6636,  6968,  7260,  7552, 7844,  8136,  8428,  8440,  8796,  9152,  9508,  9864, 10220]));//forgefmt: disable-line
        C[34] = fromAbiEncoded(abi.encode([ 1248,  1284,  1320,  1356,  1392,  1428,  1464,  2944,  3044, 3144,  3244,  3344,  3444,  3544,  4640,  4804,  4968,  5132, 5296,  5460,  5624,  6336,  6564,  6792,  7020,  7248,  7476, 7704,  8032,  8324,  8616,  8908,  9200,  9492,  9784,  9728, 10084, 10440, 10796, 11152, 11508, 11864, 11424, 11844, 12264, 12684, 13104, 13524, 13944]));//forgefmt: disable-line
        C[35] = fromAbiEncoded(abi.encode([ 1416,  1452,  1488,  1524,  1560,  1596,  1632,  1668,  3336, 3436,  3536,  3636,  3736,  3836,  3936,  4036,  5256,  5420, 5584,  5748,  5912,  6076,  6240,  6404,  7176,  7404,  7632, 7860,  8088,  8316,  8544,  8772,  9096,  9388,  9680,  9972, 10264, 10556, 10848, 11140, 11016, 11372, 11728, 12084, 12440, 12796, 13152, 13508, 12936, 13356, 13776, 14196, 14616, 15036, 15456, 15876, 14856, 15340, 15824, 16308, 16792, 17276, 17760, 18244]));//forgefmt: disable-line

        uint256 k;

        for (uint256 m = 1; m < 9; m++) {
            for (uint256 n = 1; n < m + 1; n++) {
                A = range(1, 1 + n * m).reshape(n, m);
                B = range(2, 2 + n * m).reshape(m, n);

                assertEq(A.dot(B), C[k++].reshape(n, n));
            }
        }
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

    function test_fromAbiEncoded() public {
        UM256 A = fromArray(MATRIX_43);
        UM256 B = fromAbiEncoded(abi.encode(MATRIX_43), 4, 3);

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
        UM256 B = fromAbiEncoded(A.bytes_(), 4, 3);

        assertEq(A, B);

        B = fromAbiEncoded_(A.bytes_(), 4, 3);
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

    /* ------------- utils ------------- */

    function affineMap(uint256 a) internal pure returns (uint256) {
        return a * 3 + 1;
    }
}

contract TestGasUM256 {
    /* ------------- constructors ------------- */

    function test_perf_zeros_128() public pure {
        zeros(128, 128);
    }

    function test_perf_ones_128() public pure {
        ones(128, 128);
    }

    function test_perf_eye_128() public pure {
        eye(128, 128);
    }

    function test_perf_full_128() public pure {
        full(128, 128, 1);
    }

    function test_perf_range_1024() public pure {
        range(1024);
    }

    /* ------------- Mat -> Scalar operators ------------- */

    function test_perf_sum_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.sum();
    }

    function test_perf_min_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.min();
    }

    function test_perf_max_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.max();
    }

    function test_perf_minMax_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.minMax();
    }

    /* ------------- Mat x Scalar -> Scalar operators ------------- */

    // todo: not good test
    function test_perf_eqAllScalar_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.eqAllScalar(1);
    }

    function test_perf_ltAllScalar_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.ltAllScalar(100);
    }

    function test_perf_gtAllScalar_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.gtAllScalar(100);
    }

    /* ------------- Mat x Mat -> Scalar operators ------------- */

    function test_perf_eq_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.eqAll(B);
    }

    /* ------------- Mat -> Mat operators ------------- */

    function test_perf_transpose_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.transpose();
    }

    function test_perf_map_128() public {
        UM256 A = mallocUM256(128, 128);

        A.map(affineMap);
    }

    /* ------------- Mat x Scalar -> Mat operators ------------- */

    function test_perf_addScalarUnchecked_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.addScalarUnchecked(1);
    }

    function test_perf_mulScalarUnchecked_128() public pure {
        UM256 A = mallocUM256(128, 128);

        A.mulScalarUnchecked(1);
    }

    function test_perf_fill_1024() public pure {
        UM256 A = mallocUM256(128, 128);

        A.fill_(1);
    }

    /* ------------- Mat x Mat -> Mat operators ------------- */

    // todo: add -> addUnchecked
    function test_perf_add_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.add(B);
    }

    function test_perf_dot_16() public pure {
        UM256 A = mallocUM256(16, 16);
        UM256 B = mallocUM256(16, 16);

        A.dot(B);
    }

    function test_perf_dot_32() public pure {
        UM256 A = mallocUM256(32, 32);
        UM256 B = mallocUM256(32, 32);

        A.dot(B);
    }

    function test_perf_dot_64() public pure {
        UM256 A = mallocUM256(64, 64);
        UM256 B = mallocUM256(64, 64);

        A.dot(B);
    }

    function test_perf_dot_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.dot(B);
    }

    function test_perf_dotTransposed_128() public pure {
        UM256 A = mallocUM256(128, 128);
        UM256 B = mallocUM256(128, 128);

        A.dotTransposed(B);
    }

    /* ------------- utils ------------- */

    function affineMap(uint256 a) internal pure returns (uint256) {
        return a * 3 + 1;
    }
}

// contract TestMemSafe is TestHelper {
//     /* ------------- memory safety ------------- */

//     modifier testMemorySafe(UM256 A) {
//         memSafeTestMat = A;

//         uint256 loc1 = freeMemPtr();
//         // Skip magic valaue at `loc1`.
//         // Skip matrix bytes length encoding.
//         // Skip matrix data encoding.
//         uint256 loc2 = loc1 + 32 + (1 + A.length()) * 32;

//         storeMagicValueAt(loc1);
//         storeMagicValueAt(loc2);

//         // Set the free memory pointer to after the first magic value.
//         setFreeMemPtr(loc1 + 32);

//         _;

//         // Make sure both magic values can be safely retrieved.
//         bytes32 v1 = mload(loc1);
//         bytes32 v2 = mload(loc2);

//         assertEq(v1, _MAGIC_VALUE, "Magic Value not found");
//         assertEq(v2, _MAGIC_VALUE, "Magic Value not found");
//     }

//     function test_addScalarUnchecked_memory_safe() public testMemorySafe(fromArray(MATRIX_43)) {
//         memSafeTestMat.addScalarUnchecked(1);
//     }

//     function test_mulScalarUnchecked_memory_safe() public testMemorySafe(fromArray(MATRIX_43)) {
//         memSafeTestMat.mulScalarUnchecked(1);
//     }

//     // function test_add_memory_safe() public testMemorySafe(fromArray(MATRIX_43)) {
//     //     memSafeTestMat.add(1);
//     // }
// }
