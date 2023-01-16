// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type N32x32 is int64;

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

uint256 constant UINT64_MAX = 0xffffffffffffffff;

error N32x32_Overflow();
error Undefined();

using {add, sub, mul, div, divUp, neg, sign, abs, eq, neq, shr, shl, lte, unwrap} for N32x32 global;

function safeCastToN32x32(int256 uc) pure returns (N32x32 c) {
    unchecked {
        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MAX) revert N32x32_Overflow();

        c = wrap(int64(uc));
    }
}

/* ------------- math operators ------------- */

function add(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = int256(unwrap(a)) + unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MAX) revert N32x32_Overflow();

        c = wrap(int64(uc));
    }
}

function sub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = int256(unwrap(a)) - unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MAX) revert N32x32_Overflow();

        c = wrap(int64(uc));
    }
}

function mul(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = (int256(unwrap(a)) * unwrap(b)) >> 32;

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MAX) revert N32x32_Overflow();

        c = wrap(int64(uc));
    }
}

function div(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = (int256(unwrap(a)) << 32) / unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MAX) revert N32x32_Overflow();

        c = wrap(int64(uc));
    }
}

function divUp(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        int256 uc = ((int256(unwrap(a)) << 32) + unwrap(b) - 1) / unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MAX) revert N32x32_Overflow();

        c = wrap(int64(uc));
    }
}

/* ------------- single operators ------------- */

function sign(N32x32 a) pure returns (N32x32 c) {
    c = unwrap(a) < 0 ? NEG_ONE : ONE;
}

function abs(N32x32 a) pure returns (N32x32 c) {
    c = unwrap(a) < 0 ? neg(a) : a;
}

function neg(N32x32 a) pure returns (N32x32 c) {
    c = wrap(-unwrap(a));
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

function toN32x32(int256 a) pure returns (N32x32 c) {
    assembly {
        c := shl(32, a)
    }
}

function fromN32x32(int256 a) pure returns (N32x32 c) {
    assembly {
        c := shl(32, a)
    }
}

function unwrap(N32x32 a) pure returns (int64 c) {
    c = N32x32.unwrap(a);
}

function wrap(int64 a) pure returns (N32x32 c) {
    c = N32x32.wrap(a);
}

/* ------------- bitwise operators ------------- */

function shl(N32x32 a, uint256 bits) pure returns (N32x32 c) {
    c = wrap(unwrap(a) << uint64(bits));
}

function shr(N32x32 a, uint256 bits) pure returns (N32x32 c) {
    c = wrap(unwrap(a) >> bits);
}

/* ------------- unchecked operators ------------- */

function uncheckedAdd(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = wrap(unwrap(a) + unwrap(b));
    }
}

function uncheckedSub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = wrap(unwrap(a) - unwrap(b));
    }
}
