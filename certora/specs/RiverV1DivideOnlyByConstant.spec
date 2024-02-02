import "Sanity.spec";
import "CVLMath.spec";
import "MathSummaries.spec";
import "Base.spec";

use rule method_reachability;

methods {
    function _.mulDivDown(uint256 a, uint256 b, uint256 c) internal => mulDivDownAbstractPlus(a, b, c) expect uint256 ALL;
    function math.mulDiv(uint256 a, uint256 b, uint256 c) internal returns (uint256) => mulDivLIA(a, b, c);
}

// @title It is never benefitial for any user to deposit in multiple smaller patches instead of one big patch.
rule depositAdditivitySplittingNotProfitable(env e1, env e2, env eSum) {
    mathint amount1;
    mathint amount2;
    address recipient;

    requireInvariant noAssetsNoShares();
    requireInvariant noAssetsNoSharesUser(recipient);
    sharesAdditivityBound(e1.msg.value, e2.msg.value, totalSupply(), totalUnderlyingSupply());

    require amount1 == to_mathint(e1.msg.value);
    require amount2 == to_mathint(e2.msg.value);
    require amount1 + amount2 == to_mathint(eSum.msg.value);

    mathint sharesBefore = balanceOf(recipient);

    storage initial = lastStorage;

    depositAndTransfer(e1, recipient);
    mathint shares1 = balanceOf(recipient);

    depositAndTransfer(e2, recipient);
    mathint shares2 = balanceOf(recipient);

    depositAndTransfer(eSum, recipient) at initial;
    mathint sharesSum = balanceOf(recipient);

    assert shares2 - sharesSum <= 2;
}
