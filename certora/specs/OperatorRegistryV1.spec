import "Sanity.spec";
import "CVLMath.spec";
import "OperatorRegistryV1_base.spec";

use rule method_reachability;

// -------- SIMPLE RULE --------

// fails due to a missing require (~ 1m)
// https://prover.certora.com/output/6893/80a8b0f027fb418db743f818dc972546/?anonymousKey=61806eefa552e16a59572d3b87faa7f43ff134f9
rule setOperatorLimits_correctness(env e)
{
    uint256 opIndex;
    uint32 newLimit;
    uint256 _snapshotBlock;
    uint256[] _operatorIndexes = [ opIndex ];
    uint32[] _newLimits = [ newLimit ];
    setOperatorLimits(e, _operatorIndexes, _newLimits, _snapshotBlock);
    assert getOperator(opIndex).limit == newLimit;
}

// holds (~ 1m)
// https://prover.certora.com/output/6893/65e54cb043dc46328e6ce0d6b1101563/?anonymousKey=59a95b52dbc09dfcc4d0ab32fa165f4dfaf20791
rule setOperatorLimits_correctness_2(env e)
{
    uint256 opIndex;
    uint32 newLimit;
    uint256 _snapshotBlock;
    uint256[] _operatorIndexes = [ opIndex ];
    uint32[] _newLimits = [ newLimit ];
    setOperatorLimits(e, _operatorIndexes, _newLimits, _snapshotBlock);
    require require_uint256(getOperator(opIndex).latestKeysEditBlockNumber) <= _snapshotBlock;
    assert getOperator(opIndex).limit == newLimit;
}

// -------- TO SHOW MATHINT --------

// holds (< 1m)
// https://prover.certora.com/output/6893/39417d2319e7407aa0fbf457167ab85d/?anonymousKey=f7f9885cbe673df3d07c4b84fa583097e52717f1
rule addOperator_correctness(env e)
{
    string opName; address opAddress;
    mathint countBefore = getOperatorsCount();
    addOperator(e, opName, opAddress);
    mathint countAfter = getOperatorsCount();
    assert countAfter == countBefore + 1;
}

// -------- PARAMETRIC RULE --------

// loop_iter:3 (~ 3m, two methods are not reachable) https://prover.certora.com/output/6893/e8676c5640de43a98ab18d6f3f0283d8/?anonymousKey=5275eb12b741864cf26c72bb4babb861e1f0ea22
// loop_iter:4 (timeout for removeValidators) https://prover.certora.com/output/6893/c2b07ef0910e41f784059015a9d7e43f/?anonymousKey=e806e69956f171fa9bd6ef903a31a762e9dea566
rule whoCanChangeOperatorsCount(method f, env e, calldataarg args)
{
    uint countBefore = getOperatorsCount();
    f(e, args);
    uint countAfter = getOperatorsCount();
    assert countAfter > countBefore => canIncreaseOperatorsCount(f);
    assert countAfter < countBefore => canDecreaseOperatorsCount(f);
}

// method removeValidators filtered out
// loop_iter:4 holds (~ 3m) https://prover.certora.com/output/6893/0b7f2b45be1c45e59d1cc4a9783ef236/?anonymousKey=db6a54e4065c7dfcca9de18265a4ff80ea9f0c88
rule whoCanChangeOperatorsCount_2(method f, env e, calldataarg args)
filtered { f -> f.selector != sig:removeValidators(uint256,uint256[]).selector }
{
    uint countBefore = getOperatorsCount();
    f(e, args);
    uint countAfter = getOperatorsCount();
    assert countAfter > countBefore => canIncreaseOperatorsCount(f);
    assert countAfter < countBefore => canDecreaseOperatorsCount(f);
}

// TODO -------- INVARIANT --------

invariant inactiveOperatorsRemainNotFunded(uint opIndex) 
    opIndex < 3 => (!getOperator(opIndex).active => getOperator(opIndex).funded == 0)
    { 
        preserved requestValidatorExits(uint256 x) with(env e) { require x <= 2; }
        preserved pickNextValidatorsToDeposit(uint256 x) with(env e) { require x <= 1; }  
        preserved removeValidators(uint256 _index, uint256[] _indexes) with(env e) { require _indexes.length <= 1; }  
    }