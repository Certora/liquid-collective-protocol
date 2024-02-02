import "CVLMath.spec";

ghost mulDivArbitrary(uint256, uint256, uint256) returns uint256;
ghost mapping(uint256 => mapping(uint256 => uint256)) _mulDivGhost {
    /// Monotonically increasing
    axiom forall uint256 xy1. forall uint256 xy2. forall uint256 z.
        xy1 <= xy2 => _mulDivGhost[xy1][z] <= _mulDivGhost[xy2][z];
    /// Monotonically decreasing
    axiom forall uint256 xy. forall uint256 z1. forall uint256 z2.
        z1 <= z2 => _mulDivGhost[xy][z1] >= _mulDivGhost[xy][z2];
}

function mulDivLIA(uint256 x, uint256 y, uint256 z) returns uint256 {
    require z !=0;
    uint256 xy = require_uint256(x * y);
    if(z > x) {
        uint256 w = assert_uint256(z - x);
        uint256 wy = require_uint256(w * y); 
        /// [(x * y) / z] + [(z - x) * y / z] = y
        /// muldiv(x , y , z) + muldiv((z-x) , y , z) <= y
        require _mulDivGhost[xy][z] + _mulDivGhost[wy][z] <= to_mathint(y);
    }
    require _mulDivGhost[xy][z] <= xy;   
    require xy < z => _mulDivGhost[xy][z] == 0;
    require xy == z => _mulDivGhost[xy][z] == 1;
    require y <= z => _mulDivGhost[xy][z] <= x;
    require x <= z => _mulDivGhost[xy][z] <= y;
    require y == z => _mulDivGhost[xy][z] == x;
    require x == z => _mulDivGhost[xy][z] == y;
    return _mulDivGhost[xy][z];
}

rule mulDivLIACheck(uint256 x, uint256 y, uint256 z) {
    require z != 0;
    uint256 result = require_uint256((x * y) / z);
    if(z > x) {
        uint256 w = assert_uint256(z - x);
        uint256 resultP = require_uint256((w * y) / z); 
        assert result + resultP <= to_mathint(y);
    }
    assert to_mathint(result) <= x * y;       
    assert x * y < to_mathint(z) => result == 0;
    assert x * y == to_mathint(z) => result == 1;
    assert y <= z => result <= x;
    assert x <= z => result <= y;
    assert y == z => result == x;
    assert x == z => result == y;
}

rule mulDivMonotonicCheck(uint256 x, uint256 y, uint256 z) {
    require z !=0;
    uint256 xp; uint256 yp; uint256 zp;
    require zp !=0;
    uint256 result = require_uint256((x * y) / z);
    uint256 resultp = require_uint256((x * y) / zp);

    assert x * y <= xp * yp  && z == zp => result <= resultp;
    assert x * y == xp * yp && z <= zp => result >= resultp;
}

function sharesAdditivityBound(uint256 amountX, uint256 amountY, uint256 S, uint256 B) {
    /// First step: Shares minted for (dx) 
    uint256 dSx = B == 0 ? amountX : _mulDivGhost[require_uint256(amountX * S)][B];
    /// Update balance (+ dx)
    uint256 B_new = require_uint256(B + amountX);
    /// Update total supply ( + dSx)
    uint256 S_new = require_uint256(S + dSx);
    /// Second step: Shares minted for (dy).
    uint256 dSy = _mulDivGhost[require_uint256(amountY * S_new)][B_new];

    /// Combined: Shares minted for (dy + dx)
    uint256 amountXY = require_uint256(amountX + amountY);
    uint256 dSxy = B == 0 ? amountXY : _mulDivGhost[require_uint256(amountXY * S)][B];

    /// The delta between splitting and combined is bounded by:
    /// -2 <= DELTA <= 2 + (dy + 1)/(B + dx)
    mathint Bound = B == 0 ? 1 : 2 + (amountY + 1) / (B_new);
    require -2 <= dSxy - (dSx + dSy) && dSxy - (dSx + dSy) <= Bound;
}

/// https://prover.certora.com/output/41958/e74e0d3601124542a4b15971f16232a3/?anonymousKey=59d38b8711234cb86cc0967af7e70519218c6c02
rule mulDivAdditivity(uint256 dx, uint256 dy) {
    uint256 B;  /// Balance
    uint256 S;  /// Shares
    require B !=0 <=> S != 0;
    /// First step: Shares minted for (dx) 
    uint256 dSx = B == 0 ? dx : mulDivDownAbstractPlus(dx,S,B);
    /// Update balance (+ dx)
    uint256 B_new = require_uint256(B + dx);
    /// Update total supply ( + dSx)
    uint256 S_new = require_uint256(S + dSx);
    /// Second step: Shares minted for (dy).
    uint256 dSy = mulDivDownAbstractPlus(dy,S_new,B_new);

    /// Combined: Shares minted for (dy + dx)
    uint256 dz = require_uint256(dx + dy);
    uint256 dSxy = B == 0 ? dz : mulDivDownAbstractPlus(dz,S,B);

    /// The delta between splitting and combined is bounded by:
    /// -2 <= DELTA <= 2 + (dy + 1)/(B + dx)
    mathint Bound = B == 0 ? 1 : 2 + (dy + 1) / (B_new);
    assert -2 <= dSxy - (dSx + dSy) && dSxy - (dSx + dSy) <= Bound;

    /// So the profit in shares is at most:
    /// 2 + (second amount + 1) / (initial balance + first amount)
}
