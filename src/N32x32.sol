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

uint256 constant MASK = 0xffffffffffffffff;

error Overflow();
error Underflow();
error Undefined();

using {add, sub, mul, div, neg, sign, abs, eq, neq, shr, shl, lte, unwrap} for N32x32 global;

function sign(N32x32 a) pure returns (N32x32 c) {
    c = unwrap(a) < 0 ? NEG_ONE : ONE;
}

function abs(N32x32 a) pure returns (N32x32 c) {
    c = unwrap(a) < 0 ? neg(a) : a;
}

// function add(N32x32 a, N32x32 b) pure returns (N32x32 c) {
//     unchecked {
//         int256 ua;
//         int256 ub;

//         assembly {
//             ua := a
//             ub := b
//         }

//         int256 uc = ua + ub;

//         if (uc < uMIN || uc > uMAX) revert Overflow();

//         assembly {
//             c := uc
//         }
//     }
// }

// function sub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
//     unchecked {
//         int256 ua;
//         int256 ub;

//         assembly {
//             ua := a
//             ub := b
//         }

//         int256 uc = ua - ub;

//         if (uc < uMIN || uc > uMAX) revert Overflow();

//         assembly {
//             c := uc
//         }
//     }
// }

// function abs(N32x32 a) pure returns (N32x32 c) {
//     unchecked {
//         int256 ua = ;

//         assembly {
//             ua := a
//         }

//         if (ua == uMIN) revert Overflow();

//         assembly {
//             if gt(a, uMAX) {

//             }
//         }

//         return a < 0 ? -a : a;
//     }
// }

// function unwrap(N32x32 a) pure returns (int64 c) {
//     return N32x32.unwrap()
// }

// function lt(N32x32 a, N32x32 b) pure returns (N32x32 c) {}

function mul(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    // unchecked {
    int256 uc = (int256(a.unwrap()) * b.unwrap()) >> 32;

    if (uc < uMIN || uc > uMAX) revert Overflow();

    c = wrap(int64(uc));
}

function div(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    int256 ub = int256(b.unwrap());

    if (ub == 0) revert Undefined();

    int256 uc = (int256(a.unwrap()) << 32) / ub;

    if (uc < uMIN || uc > uMAX) revert Overflow();

    c = wrap(int64(uc));
}

// function neg(N32x32 a) pure returns (N32x32 c) {
//     assembly {
//         c := and(add(not(a), 1), MASK)
//     }
// }

/* ------------- comparators ------------- */

// function eq(N32x32 a, N32x32 b) pure returns (bool res) {
//     assembly {
//         res := eq(a, b)
//     }
// }

// function neq(N32x32 a, N32x32 b) pure returns (bool res) {
//     assembly {
//         res := iszero(eq(a, b))
//     }
// }

// function gt(N32x32 a, N32x32 b) pure returns (bool res) {
//     assembly {
//         res := sgt(a, b)
//     }
// }

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

/// @notice Unwraps a N32x32 number into int64.
function unwrap(N32x32 a) pure returns (int64 c) {
    c = N32x32.unwrap(a);
}

/// @notice Wraps a int64 number into the N32x32 value type.
function wrap(int64 a) pure returns (N32x32 c) {
    c = N32x32.wrap(a);
}

/// @notice Implements the checked addition operation (+) in the N32x32 type.
function add(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = wrap(unwrap(a) + unwrap(b));
}

/// @notice Implements the negation operation (-) in the N32x32 type.
function neg(N32x32 a) pure returns (N32x32 c) {
    c = wrap(-unwrap(a));
}

/// @notice Implements the AND (&) bitwise operation in the N32x32 type.
function and(N32x32 a, int64 bits) pure returns (N32x32 c) {
    c = wrap(unwrap(a) & bits);
}

/// @notice Implements the equal (=) operation in the N32x32 type.
function eq(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) == unwrap(b);
}

/// @notice Implements the greater than operation (>) in the N32x32 type.
function gt(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) > unwrap(b);
}

/// @notice Implements the greater than or equal to operation (>=) in the N32x32 type.
function gte(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) >= unwrap(b);
}

/// @notice Implements a zero comparison check function in the N32x32 type.
function isZero(N32x32 a) pure returns (bool c) {
    c = unwrap(a) == 0;
}

/// @notice Implements the left shift operation (<<) in the N32x32 type.
function shl(N32x32 a, uint256 bits) pure returns (N32x32 c) {
    c = wrap(unwrap(a) << uint64(bits));
}

/// @notice Implements the lower than operation (<) in the N32x32 type.
function lt(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) < unwrap(b);
}

/// @notice Implements the lower than or equal to operation (<=) in the N32x32 type.
function lte(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) <= unwrap(b);
}

/// @notice Implements the unchecked modulo operation (%) in the N32x32 type.
function mod(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = wrap(unwrap(a) % unwrap(b));
}

/// @notice Implements the not equal operation (!=) in the N32x32 type.
function neq(N32x32 a, N32x32 b) pure returns (bool c) {
    c = unwrap(a) != unwrap(b);
}

/// @notice Implements the OR (|) bitwise operation in the N32x32 type.
function or(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = wrap(unwrap(a) | unwrap(b));
}

/// @notice Implements the right shift operation (>>) in the N32x32 type.
function shr(N32x32 a, uint256 bits) pure returns (N32x32 c) {
    c = wrap(unwrap(a) >> bits);
}

/// @notice Implements the checked subtraction operation (-) in the N32x32 type.
function sub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = wrap(unwrap(a) - unwrap(b));
}

/// @notice Implements the unchecked addition operation (+) in the N32x32 type.
function uncheckedAdd(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = wrap(unwrap(a) + unwrap(b));
    }
}

/// @notice Implements the unchecked subtraction operation (-) in the N32x32 type.
function uncheckedSub(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    unchecked {
        c = wrap(unwrap(a) - unwrap(b));
    }
}

/// @notice Implements the unchecked unary minus operation (-) in the N32x32 type.
function uncheckedUnary(N32x32 a) pure returns (N32x32 c) {
    unchecked {
        c = wrap(-unwrap(a));
    }
}

/// @notice Implements the XOR (^) bitwise operation in the N32x32 type.
function xor(N32x32 a, N32x32 b) pure returns (N32x32 c) {
    c = wrap(unwrap(a) ^ unwrap(b));
}
