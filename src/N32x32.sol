// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type N32x32 is int64;

using N32x32Lib for N32x32 global;

library N32x32Lib {
    // Constants.
    N32x32 constant ZERO = N32x32.wrap(0);

    int64 constant uHALF = 0x80000000;
    N32x32 constant HALF = N32x32.wrap(uHALF);

    int64 constant uONE = 0x100000000;
    N32x32 constant ONE = N32x32.wrap(uONE);

    int64 constant uTWO = 0x200000000;
    N32x32 constant TWO = N32x32.wrap(uTWO);

    int64 constant uNEG_ONE = -0x100000000;
    N32x32 constant NEG_ONE = N32x32.wrap(uNEG_ONE);

    int64 constant uNEG_TWO = -0x200000000;
    N32x32 constant NEG_TWO = N32x32.wrap(uNEG_TWO);

    int64 constant uMAX = 0x7fffffffffffffff;
    N32x32 constant MAX = N32x32.wrap(uMAX);

    int64 constant uMIN = -0x8000000000000000;
    N32x32 constant MIN = N32x32.wrap(uMIN);

    int64 constant uHALF_MAX = 0x3fffffffffffffff;
    N32x32 constant HALF_MAX = N32x32.wrap(uHALF_MAX);

    int64 constant uHALF_MIN = -0x4000000000000000;
    N32x32 constant HALF_MIN = N32x32.wrap(uHALF_MIN);

    int256 constant INT32_MAX = 0x7fffffff;
    int256 constant INT32_MIN = -0x80000000;
    int256 constant INT32_SIGN = 0x80000000;
    int256 constant INT64_SIGN = 0x8000000000000000;
    int256 constant INT64_MAX = 0x7fffffffffffffff;

    int256 constant INT32_MAX_WAD = 0x6f05b59c5d1494c589c0000;

    uint256 constant UINT32_MAX = 0xffffffff;
    uint256 constant UINT64_MAX = 0xffffffffffffffff;

    uint256 constant MASK_2X4 = 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff;
    uint256 constant INT64_SIGN_X4 = 0x8000000000000000800000000000000080000000000000008000000000000000;

    // Errors.
    error Overflow();
    error Undefined();

    /* ------------- math operators ------------- */

    function add(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            int256 uc = int256(unwrap(a)) + unwrap(b);

            if (uint256(uc) + uint256(INT64_SIGN) > UINT64_MAX) revert Overflow();

            c = N32x32.wrap(int64(uc));
        }
    }

    function addUnchecked(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            c = N32x32.wrap(unwrap(a) + unwrap(b));
        }
    }

    function sub(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            int256 uc = int256(unwrap(a)) - unwrap(b);

            if (uint256(uc) + uint256(INT64_SIGN) > UINT64_MAX) revert Overflow();

            c = N32x32.wrap(int64(uc));
        }
    }

    function mul(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            int256 uc = (int256(unwrap(a)) * unwrap(b)) >> 32;

            if (uint256(uc) + uint256(INT64_SIGN) > UINT64_MAX) revert Overflow();

            c = N32x32.wrap(int64(uc));
        }
    }

    function mulUnchecked(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            c = N32x32.wrap(int64(int256(unwrap(a)) * unwrap(b) >> 32));
        }
    }

    function squared(N32x32 a) internal pure returns (N32x32 c) {
        unchecked {
            int256 uc = (int256(unwrap(a)) * unwrap(a)) >> 32;

            if (uint256(uc) + uint256(INT64_SIGN) > UINT64_MAX) revert Overflow();

            c = N32x32.wrap(int64(uc));
        }
    }

    function squaredUnchecked(N32x32 a) internal pure returns (N32x32 c) {
        unchecked {
            c = N32x32.wrap(int64(int256(unwrap(a)) * unwrap(a) >> 32));
        }
    }

    function div(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            int256 uc = (int256(unwrap(a)) << 32) / unwrap(b);

            if (uint256(uc) + uint256(INT64_SIGN) > UINT64_MAX) revert Overflow();

            c = N32x32.wrap(int64(uc));
        }
    }

    function divUp(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        unchecked {
            int256 uc = ((int256(unwrap(a)) << 32) + unwrap(b) - 1) / unwrap(b);

            if (uint256(uc) + uint256(INT64_SIGN) > UINT64_MAX) revert Overflow();

            c = N32x32.wrap(int64(uc));
        }
    }

    function max(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        c = unwrap(a) > unwrap(b) ? a : b;
    }

    function min(N32x32 a, N32x32 b) internal pure returns (N32x32 c) {
        c = unwrap(a) < unwrap(b) ? a : b;
    }

    /* ------------- math operators (try) ------------- */

    function tryAdd(N32x32 a, N32x32 b) internal pure returns (bool success, N32x32 c) {
        unchecked {
            int256 uc = int256(unwrap(a)) + unwrap(b);

            success = uint256(uc) + uint256(INT64_SIGN) >> 64 == 0;

            c = N32x32.wrap(int64(uc));
        }
    }

    function trySub(N32x32 a, N32x32 b) internal pure returns (bool success, N32x32 c) {
        unchecked {
            int256 uc = int256(unwrap(a)) - unwrap(b);

            success = uint256(uc) + uint256(INT64_SIGN) >> 64 == 0;

            c = N32x32.wrap(int64(uc));
        }
    }

    function tryMul(N32x32 a, N32x32 b) internal pure returns (bool success, N32x32 c) {
        unchecked {
            int256 uc = (int256(unwrap(a)) * unwrap(b)) >> 32;

            success = uint256(uc) + uint256(INT64_SIGN) >> 64 == 0;

            c = N32x32.wrap(int64(uc));
        }
    }

    function tryDiv(N32x32 a, N32x32 b) internal pure returns (bool success, N32x32 c) {
        unchecked {
            int256 uc = (int256(unwrap(a)) << 32) / unwrap(b);

            success = uint256(uc) + uint256(INT64_SIGN) >> 64 == 0;

            c = N32x32.wrap(int64(uc));
        }
    }

    /* ------------- math operators (overloads) ------------- */

    function addInt(N32x32 a, int256 ub) internal pure returns (N32x32 c) {
        c = add(a, fromInt(ub));
    }

    function subInt(N32x32 a, int256 ub) internal pure returns (N32x32 c) {
        c = sub(a, fromInt(ub));
    }

    function mulInt(N32x32 a, int256 ub) internal pure returns (N32x32 c) {
        c = mul(a, fromInt(ub));
    }

    function divInt(N32x32 a, int256 ub) internal pure returns (N32x32 c) {
        c = div(a, fromInt(ub));
    }

    /* ------------- single operators ------------- */

    function sign(N32x32 a) internal pure returns (N32x32 c) {
        c = unwrap(a) < 0 ? NEG_ONE : ONE;
    }

    function abs(N32x32 a) internal pure returns (N32x32 c) {
        c = unwrap(a) < 0 ? neg(a) : a;
    }

    function neg(N32x32 a) internal pure returns (N32x32 c) {
        c = N32x32.wrap(-unwrap(a));
    }

    /* ------------- comparators ------------- */

    function eq(N32x32 a, N32x32 b) internal pure returns (bool c) {
        c = unwrap(a) == unwrap(b);
    }

    function neq(N32x32 a, N32x32 b) internal pure returns (bool c) {
        c = unwrap(a) != unwrap(b);
    }

    function lt(N32x32 a, N32x32 b) internal pure returns (bool c) {
        c = unwrap(a) < unwrap(b);
    }

    function lte(N32x32 a, N32x32 b) internal pure returns (bool c) {
        c = unwrap(a) <= unwrap(b);
    }

    function gt(N32x32 a, N32x32 b) internal pure returns (bool c) {
        c = unwrap(a) > unwrap(b);
    }

    function gte(N32x32 a, N32x32 b) internal pure returns (bool c) {
        c = unwrap(a) >= unwrap(b);
    }

    function isZero(N32x32 a) internal pure returns (bool c) {
        c = unwrap(a) == 0;
    }

    function isNegative(N32x32 a) internal pure returns (bool c) {
        c = unwrap(a) < 0;
    }

    function isPositive(N32x32 a) internal pure returns (bool c) {
        c = unwrap(a) >= 0;
    }

    /* ------------- conversion ------------- */

    function fromInt(int256 a) internal pure returns (N32x32 c) {
        unchecked {
            if (uint256(a) + uint256(INT32_SIGN) > UINT32_MAX) revert Overflow();

            c = N32x32.wrap(int64(a) << 32);
        }
    }

    function fromInt64(int64 a) internal pure returns (N32x32 c) {
        unchecked {
            if (uint256(int256(a)) + uint256(INT32_SIGN) > UINT32_MAX) revert Overflow();

            c = N32x32.wrap(a << 32);
        }
    }

    function fromInt32(int32 a) internal pure returns (N32x32 c) {
        c = N32x32.wrap(int64(a) << 32);
    }

    function fromUint(uint256 a) internal pure returns (N32x32 c) {
        if (a > uint256(INT32_MAX)) revert Overflow();

        c = N32x32.wrap(int64(int256(a) << 32));
    }

    function fromUint64(uint64 a) internal pure returns (N32x32 c) {
        if (a > uint256(INT32_MAX)) revert Overflow();

        c = N32x32.wrap(int64(a) << 32); // TODO does this include cleaning the result after shifting??
    }

    function fromUint32(uint32 a) internal pure returns (N32x32 c) {
        if (a > uint256(int256(INT32_MAX))) revert Overflow();

        c = N32x32.wrap(int64(int32(a)) << 32);
    }

    function fromWAD(uint256 a) internal pure returns (N32x32 c) {
        if (a > uint256(INT32_MAX_WAD)) revert Overflow();

        c = N32x32.wrap(int64((int256(a) << 32) / 1e18)); // TODO does this include zero check?
    }

    function toInt(N32x32 a) internal pure returns (int256 c) {
        assembly {
            c := sar(32, a)
        }
    }

    function toInt32(N32x32 a) internal pure returns (int32 c) {
        assembly {
            c := sar(32, a)
        }
    }

    function toInt64(N32x32 a) internal pure returns (int64 c) {
        assembly {
            c := sar(32, a)
        }
    }

    function toUint(N32x32 a) internal pure returns (uint256 c) {
        if (N32x32.unwrap(a) < 0) revert Overflow();

        assembly {
            c := shr(32, a)
        }
    }

    function toUint64(N32x32 a) internal pure returns (uint64 c) {
        if (N32x32.unwrap(a) < 0) revert Overflow();

        assembly {
            c := shr(32, a)
        }
    }

    function toUint32(N32x32 a) internal pure returns (uint32 c) {
        if (N32x32.unwrap(a) < 0) revert Overflow();

        assembly {
            c := shr(32, a)
        }
    }

    function unwrap(N32x32 a) internal pure returns (int64 c) {
        c = N32x32.unwrap(a);
    }

    /* ------------- bitwise operators ------------- */

    function shl(N32x32 a, uint256 bits) internal pure returns (N32x32 c) {
        c = N32x32.wrap(unwrap(a) << uint64(bits));
    }

    function shr(N32x32 a, uint256 bits) internal pure returns (N32x32 c) {
        c = N32x32.wrap(unwrap(a) >> bits);
    }
}
