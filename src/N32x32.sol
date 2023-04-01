// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type N32x32 is int64;

// Math operators.
using {
    add,
    addUnchecked,
    sub,
    mul,
    div,
    divUp,
    addInt,
    subInt,
    mulInt,
    divInt,
    neg,
    sign,
    abs,
    shr,
    shl
} for N32x32 global;

// Comparators.
using { eq, neq, lt, lte, gt, gte } for N32x32 global;

// Conversion.
using { toInt, toInt64, toInt32, toUint, toUint64, toUint32, unwrap } for N32x32 global;

// Errors.
error N32x32_Overflow();
error N32x32_Underflow();
error Undefined();

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

int64 constant uMAX_HALF = 0x3fffffffffffffff;
N32x32 constant MAX_HALF = N32x32.wrap(uMAX_HALF);

int64 constant uMIN_HALF = -0x4000000000000000;
N32x32 constant MIN_HALF = N32x32.wrap(uMIN_HALF);

int64 constant uMAX32 = 0x7fffffff;
N32x32 constant MAX32 = N32x32.wrap(uMAX);

int64 constant uMIN32 = -0x80000000;
N32x32 constant MIN32 = N32x32.wrap(uMIN);

uint256 constant uMAX32WAD = 0x6f05b59c5d1494c589c0000;

uint256 constant UINT32_MASK = 0xffffffff;
uint256 constant UINT64_MASK = 0xffffffffffffffff;

uint256 constant uNEG_MIN = 0x8000000000000000;

// function safeCastToN32x32(int256 uc) pure returns (N32x32 c) {
//     unchecked {
//         if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

//         c = wrap(int64(uc));
//     }
// }

/* ------------- math operators ------------- */

function add(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = int256(unwrap(a)) + unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(int64(uc));
    }
}

function addUnchecked(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = N32x32.wrap(unwrap(a) + unwrap(b));
    }
}

function sub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = int256(unwrap(a)) - unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(int64(uc));
    }
}

function mul(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = (int256(unwrap(a)) * unwrap(b)) >> 32;

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(int64(uc));
    }
}

function div(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = (int256(unwrap(a)) << 32) / unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(int64(uc));
    }
}

function divUp(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = ((int256(unwrap(a)) << 32) + unwrap(b) - 1) / unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(int64(uc));
    }
}

function max(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = unwrap(a) > unwrap(b) ? a : b;
}

function min(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = unwrap(a) < unwrap(b) ? a : b;
}

/* ------------- math operators (overloads) ------------- */

function addInt(N32x32 a, int256 ub) pure returns (N32x32 c) {
    c = add(a, N32x32FromInt(ub));
}

function subInt(N32x32 a, int256 ub) pure returns (N32x32 c) {
    c = sub(a, N32x32FromInt(ub));
}

function mulInt(N32x32 a, int256 ub) pure returns (N32x32 c) {
    c = mul(a, N32x32FromInt(ub));
}

function divInt(N32x32 a, int256 ub) pure returns (N32x32 c) {
    c = div(a, N32x32FromInt(ub));
}

/* ------------- single operators ------------- */

function sign(N32x32 a) pure returns (N32x32 c) {
    c = unwrap(a) < 0 ? NEG_ONE : ONE;
}

function abs(N32x32 a) pure returns (N32x32 c) {
    c = unwrap(a) < 0 ? neg(a) : a;
}

function neg(N32x32 a) pure returns (N32x32 c) {
    c = N32x32.wrap(-unwrap(a));
}

/* ------------- comparators ------------- */

function eq(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) == unwrap(b);
}

function neq(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) != unwrap(b);
}

function lt(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) < unwrap(b);
}

function lte(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) <= unwrap(b);
}

function gt(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) > unwrap(b);
}

function gte(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) >= unwrap(b);
}

function isZero(N32x32 a) pure returns (bool c) {
    c = unwrap(a) == 0;
}

/* ------------- conversion ------------- */

function N32x32FromInt(int256 a) pure returns (N32x32 c) {
    unchecked {
        if (uint256(a) - uint256(int256(uMIN32)) > UINT32_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(int64(a) << 32);
    }
}

function N32x32FromInt64(int64 a) pure returns (N32x32 c) {
    unchecked {
        if (uint256(int256(a)) - uint256(int256(uMIN32)) > UINT32_MASK) revert N32x32_Overflow();

        c = N32x32.wrap(a << 32);
    }
}

function N32x32FromInt32(int32 a) pure returns (N32x32 c) {
    c = N32x32.wrap(int64(a) << 32);
}

function N32x32FromUint(uint256 a) pure returns (N32x32 c) {
    if (a > uint256(int256(uMAX32))) revert N32x32_Overflow();

    c = N32x32.wrap(int64(int256(a)) << 32);
}

function N32x32FromUint64(uint64 a) pure returns (N32x32 c) {
    if (a > uint256(int256(uMAX32))) revert N32x32_Overflow();

    c = N32x32.wrap(int64(a) << 32);
}

function N32x32FromUint32(uint32 a) pure returns (N32x32 c) {
    if (a > uint256(int256(uMAX32))) revert N32x32_Overflow();

    c = N32x32.wrap(int64(int32(a)) << 32);
}

function N32x32FromWAD(uint256 a) pure returns (N32x32 c) {
    if (a > uMAX32WAD) revert N32x32_Overflow();

    c = N32x32.wrap(int64((int256(a) << 32) / 1e18));
}

function toInt(N32x32 a) pure returns (int256 c) {
    assembly {
        c := sar(32, a)
    }
}

function toInt32(N32x32 a) pure returns (int32 c) {
    assembly {
        c := sar(32, a)
    }
}

function toInt64(N32x32 a) pure returns (int64 c) {
    assembly {
        c := sar(32, a)
    }
}

function toUint(N32x32 a) pure returns (uint256 c) {
    if (N32x32.unwrap(a) < 0) revert N32x32_Underflow();

    assembly {
        c := shr(32, a)
    }
}

function toUint64(N32x32 a) pure returns (uint64 c) {
    if (N32x32.unwrap(a) < 0) revert N32x32_Underflow();

    assembly {
        c := shr(32, a)
    }
}

function toUint32(N32x32 a) pure returns (uint32 c) {
    if (N32x32.unwrap(a) < 0) revert N32x32_Underflow();

    assembly {
        c := shr(32, a)
    }
}

function unwrap(N32x32 a) pure returns (int64 c) {
    c = N32x32.unwrap(a);
}

// function N32x32SafeWrapInt(int256 a) pure returns (N32x32 c) {
//     if (uint256(a) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

//     c = N32x32.wrap(int64(int256(a)));
// }

// function N32x32SafeWrapUint(uint256 a) pure returns (N32x32 c) {
//     if (a > uint256(int256(uMAX))) revert N32x32_Overflow();

//     c = N32x32.wrap(int64(int256(a)));
// }

/* ------------- bitwise operators ------------- */

function shl(N32x32 a, uint256 bits) pure returns (N32x32 c) {
    c = N32x32.wrap(unwrap(a) << uint64(bits));
}

function shr(N32x32 a, uint256 bits) pure returns (N32x32 c) {
    c = N32x32.wrap(unwrap(a) >> bits);
}

/* ------------- unchecked operators ------------- */

function uncheckedAdd(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = N32x32.wrap(unwrap(a) + unwrap(b));
    }
}

function uncheckedSub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = N32x32.wrap(unwrap(a) - unwrap(b));
    }
}
