import "Sanity.spec";
import "CVLMath.spec";
import "OperatorRegistryV1_base.spec";

use rule method_reachability;

rule whoCanChangeOperatorsCount(method f, env e, calldataarg args)
{
    uint countBefore = getOperatorsCount();
    f(e, args);
    uint countAfter = getOperatorsCount();
    assert countAfter > countBefore => canIncreaseOperatorsCount(f);
    assert countAfter < countBefore => canDecreaseOperatorsCount(f);
}

// LI3: https://prover.certora.com/output/6893/a063f8f6e66b465699c7f21687781e9d/?anonymousKey=a86c03927f223d2255cadffcb83c5c4867d5ba1a
rule whoCanChangeOperatorsCount_2(method f, env e, calldataarg args)
{
    uint countBefore = getOperatorsCount();
    require countBefore <= 3;
    f(e, args);
    uint countAfter = getOperatorsCount();
    assert countAfter > countBefore => canIncreaseOperatorsCount(f);
    assert countAfter < countBefore => canDecreaseOperatorsCount(f);
}

invariant inactiveOperatorsRemainNotFunded(uint opIndex) 
    isOpIndexInBounds(opIndex) => 
        (!getOperator(opIndex).active => getOperator(opIndex).funded == 0)
    { 
        preserved requestValidatorExits(uint256 x) with(env e) { require x <= 2; }
        preserved pickNextValidatorsToDeposit(uint256 x) with(env e) { require x <= 1; }  
        preserved removeValidators(uint256 _index, uint256[] _indexes) with(env e) { require _indexes.length <= 1; }  
    }
 


