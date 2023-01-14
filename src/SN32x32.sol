// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";

type SN32x32 is int64;

SN32x32 constant ZERO = SN32x32.wrap(0);

int64 constant uHALF = 0x80000000;
SN32x32 constant HALF = SN32x32.wrap(uHALF);

int64 constant uONE = 0x100000000;
SN32x32 constant ONE = SN32x32.wrap(uONE);

int64 constant uTWO = 0x200000000;
SN32x32 constant TWO = SN32x32.wrap(uTWO);

int64 constant uNEG_ONE = -0x100000000;
SN32x32 constant NEG_ONE = SN32x32.wrap(uNEG_ONE);

int64 constant uNEG_TWO = -0x200000000;
SN32x32 constant NEG_TWO = SN32x32.wrap(uNEG_TWO);

int64 constant uMAX = 0x7fffffffffffffff;
SN32x32 constant MAX = SN32x32.wrap(uMAX);

int64 constant uMIN = -0x8000000000000000;
SN32x32 constant MIN = SN32x32.wrap(uMIN);

int64 constant uMAX_HALF = 0x3fffffffffffffff;
SN32x32 constant MAX_HALF = SN32x32.wrap(uMAX_HALF);

int64 constant uMIN_HALF = -0x4000000000000000;
SN32x32 constant MIN_HALF = SN32x32.wrap(uMIN_HALF);

uint256 constant MASK = 0xffffffffffffffff;

error Overflow();
error Undefined();

using {add, sub, mul, div, divUp, neg, sign, abs, eq, neq, shr, shl, lte, unwrap} for SN32x32 global;

function safeCastToSN32x32(int256 uc) pure returns (SN32x32 c) {
    unchecked {
        if (uint256(uc) - uint256(int256(uMIN)) > MASK) revert Overflow();

        c = wrap(int64(uc));
    }
}

/* ------------- math operators ------------- */

function add(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        int256 uc = int256(unwrap(a)) + unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > MASK) revert Overflow();

        c = wrap(int64(uc));
    }
}

function sub(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        int256 uc = int256(unwrap(a)) - unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > MASK) revert Overflow();

        c = wrap(int64(uc));
    }
}

function mul(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        int256 uc = (int256(unwrap(a)) * unwrap(b)) >> 32;

        if (uint256(uc) - uint256(int256(uMIN)) > MASK) revert Overflow();

        c = wrap(int64(uc));
    }
}

function div(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        int256 uc = (int256(unwrap(a)) << 32) / unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > MASK) revert Overflow();

        c = wrap(int64(uc));
    }
}

function divUp(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        int256 uc = ((int256(unwrap(a)) << 32) + unwrap(b) - 1) / unwrap(b);

        if (uint256(uc) - uint256(int256(uMIN)) > MASK) revert Overflow();

        c = wrap(int64(uc));
    }
}

/* ------------- single operators ------------- */

function sign(SN32x32 a) pure returns (SN32x32 c) {
    c = unwrap(a) < 0 ? NEG_ONE : ONE;
}

function abs(SN32x32 a) pure returns (SN32x32 c) {
    c = unwrap(a) < 0 ? neg(a) : a;
}

function neg(SN32x32 a) pure returns (SN32x32 c) {
    c = wrap(-unwrap(a));
}

/* ------------- comparators ------------- */

function eq(SN32x32 a, SN32x32 b) pure returns (bool c) {
    c = unwrap(a) == unwrap(b);
}

function neq(SN32x32 a, SN32x32 b) pure returns (bool c) {
    c = unwrap(a) != unwrap(b);
}

function lt(SN32x32 a, SN32x32 b) pure returns (bool c) {
    c = unwrap(a) < unwrap(b);
}

function lte(SN32x32 a, SN32x32 b) pure returns (bool c) {
    c = unwrap(a) <= unwrap(b);
}

function gt(SN32x32 a, SN32x32 b) pure returns (bool c) {
    c = unwrap(a) > unwrap(b);
}

function gte(SN32x32 a, SN32x32 b) pure returns (bool c) {
    c = unwrap(a) >= unwrap(b);
}

function isZero(SN32x32 a) pure returns (bool c) {
    c = unwrap(a) == 0;
}

/* ------------- conversion ------------- */

function toSN32x32(int256 a) pure returns (SN32x32 c) {
    assembly {
        c := shl(32, a)
    }
}

function fromSN32x32(int256 a) pure returns (SN32x32 c) {
    assembly {
        c := shl(32, a)
    }
}

function unwrap(SN32x32 a) pure returns (int64 c) {
    c = SN32x32.unwrap(a);
}

function wrap(int64 a) pure returns (SN32x32 c) {
    c = SN32x32.wrap(a);
}

/* ------------- bitwise operators ------------- */

function shl(SN32x32 a, uint256 bits) pure returns (SN32x32 c) {
    c = wrap(unwrap(a) << uint64(bits));
}

function shr(SN32x32 a, uint256 bits) pure returns (SN32x32 c) {
    c = wrap(unwrap(a) >> bits);
}

/* ------------- unchecked operators ------------- */

function uncheckedAdd(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        c = wrap(unwrap(a) + unwrap(b));
    }
}

function uncheckedSub(SN32x32 a, SN32x32 b) pure returns (SN32x32 c) {
    unchecked {
        c = wrap(unwrap(a) - unwrap(b));
    }
}
