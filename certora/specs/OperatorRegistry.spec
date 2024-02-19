/**
@title Example specification with Certora Prover. 
@note See https://docs.certora.com for a complete guide.
***/


/*
    Declaration of methods that are used in the rules. `envfree` indicates that
    the method is not dependent on the environment (`msg.value`, `msg.sender`).
    Methods that are not declared here are assumed to be dependent on the
    environment.
*/

methods {
    function getOperatorAddress(uint256) external returns(address) envfree;
    function getLatestKeysEditBlockNumber(uint256 opIndex) external 
        returns (uint64) envfree;
    function getOperator(uint256 _index) external returns (OperatorsV2.Operator) envfree;
    function getAdmin() external returns (address) envfree;

    function LibBytes.slice(bytes memory _bytes, uint256 _start, uint256 _length) internal returns (bytes memory) => bytesSliceSummary(_bytes, _start, _length);
}

function bytesSliceSummary(bytes buffer, uint256 start, uint256 len) returns bytes {
	bytes to_ret;
	return to_ret;
}


/**
    @title - integrity of a successful (non reverting) to setOperatorLimits()
    // todo - violated, undersntad why and fix  
**/
rule integritySetOperatorLimits() {
    env e; // represents global solidity variables such as msg.sender, block.timestamp 
    
    // arbitrary arguments to setOperatorLimits
    uint256[] operatorIndexes;
    uint32[] newLimits;
    uint256 snapshotBlock;
    
    // select an element from the array 
    uint256 i;
    require i < operatorIndexes.length;
    uint256 opIndex = operatorIndexes[i];
    
    setOperatorLimits(e, operatorIndexes, newLimits, snapshotBlock );
    uint32 limitAfter = getOperator(opIndex).limit;

    assert limitAfter == newLimits[i];
    
}



/** 
    @title  Revert case of setOperatorLimits
    @dev lastReverted references the last call to solidity 
**/  
rule revertSetOperatorLimits() {
    env e;
    
    uint256[] operatorIndexes;
    uint32[] newLimits;
    uint256 snapshotBlock;
    
    setOperatorLimits@withrevert(e, operatorIndexes, newLimits, snapshotBlock );
    bool reverted = lastReverted;
    // todo - is this correct? 
    assert getAdmin() == e.msg.sender || reverted; 

}


/** 
    @title Check that some case can occur 
**/  
rule witnessSetOperatorLimits() {
    uint256 i;

    uint256[] operatorIndexes;
    uint32[] newLimits;
    uint256 snapshotBlock;

    require i < operatorIndexes.length;
    uint256 opIndex = operatorIndexes[i];
    env e;

    uint32 limitBefore = getOperator(opIndex).limit;
    uint256 latestKeysEditBlockNumber = getOperator(opIndex).latestKeysEditBlockNumber;

    setOperatorLimits(e, operatorIndexes, newLimits, snapshotBlock );

    uint32 limitAfter = getOperator(opIndex).limit;

    satisfy limitAfter == limitBefore;

}

/** 
    @title Relational property - compares two cases on the same state
**/  
rule compare() {

    env e;
    uint256[] operatorIndexes;
    uint32[] newLimits;
    uint256 snapshotBlock;
    
    storage init = lastStorage;  //take a snapshot of the storage
    setOperatorLimits(e, operatorIndexes, newLimits, snapshotBlock );

    uint256 snapshotBlock2;
    setOperatorLimits@withrevert(e, operatorIndexes, newLimits, snapshotBlock2 ) at init; //back to the init state
    //todo - continue 
    assert true; 


} 


rule justAStart() {
    env e;
    calldataarg args; 
    removeValidators(e,args);
    satisfy true; 
}

rule removeValidatorsDecreaseKeysCount(env e)
{
    uint256[] indices;
    uint opIndex;
    uint keysBefore = getOperator(opIndex).keys;
    removeValidators(e, opIndex, indices);
    uint keysAfter = getOperator(opIndex).keys;
    assert keysBefore > keysAfter;
}

rule removeValidatorsDecreaseKeysAccordingly(env e)
{
    uint256[] indices;
    uint opIndex;
    uint keysBefore = getOperator(opIndex).keys;
    require keysBefore < 4;
    removeValidators(e, opIndex, indices);
    uint keysAfter = getOperator(opIndex).keys;
    assert to_mathint(keysAfter + indices.length) == to_mathint(keysBefore);
}