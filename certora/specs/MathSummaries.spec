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