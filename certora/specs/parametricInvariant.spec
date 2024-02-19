/**
    # Example specification - using parametric rules and invariants
**/

methods {
    function getOperatorsCount() external returns (uint256) envfree;
    function operatorIsActive(uint256) external returns (bool) envfree;
    function getOperator(uint256) external returns (OperatorsV2.Operator) envfree;
    function getValidatorStateByIndex(uint256, uint256) external returns (uint256) envfree;
    
    function LibBytes.slice(
        bytes memory _bytes, uint256 _start, uint256 _length
    ) internal returns (bytes memory) => bytesSliceSummary(_bytes, _start, _length);
}


function bytesSliceSummary(bytes buffer, uint256 start, uint256 len) returns bytes {
    bytes to_ret;
    return to_ret;
}


// -- Parametric rules ---------------------------------------------------------

// Needed for speed-up and some vacuity issues
definition isIgnoredMethod_Parametric(method f) returns bool = (
    f.selector == sig:pickNextValidatorsToDeposit(uint256).selector ||
    f.selector == sig:removeValidators(uint256, uint256[]).selector ||
    f.selector == sig:forceFundedValidatorKeysEventEmission(uint256).selector
);


/** 
    @title Only `addOperator` can increase the number of operators
    This is an example of a parametric rule.
    This rule is missing another function that can increase the number of operators.
**/
rule onlyAddOperatorIncreasesOperatorsNum(method f) filtered {
    f -> !(isIgnoredMethod_Parametric(f) || f.isView)
} {
    uint256 numOperatorsBefore = getOperatorsCount();

    env e;
    calldataarg args;
    f(e, args);

    uint256 numOperatorsAfter = getOperatorsCount();

    assert (
        numOperatorsAfter > numOperatorsBefore =>
        f.selector == sig:addOperator(string, address).selector ||
        f.selector == sig:initOperatorsRegistryV1_1().selector
    ), "Only addOperator can add an operator";
}


/** 
    @title The number of operators can only grow by 1
    This rule has a common type error.
**/
rule numOperatorsOnlyIncreasesByOne(method f) filtered {
    f -> !(isIgnoredMethod_Parametric(f) || f.isView)
} {
    uint256 numOperatorsBefore = getOperatorsCount();

    env e;
    calldataarg args;
    f(e, args);

    uint256 numOperatorsAfter = getOperatorsCount();

    assert (
        to_mathint(numOperatorsAfter) <=  numOperatorsBefore + 1,
        "Only one operator can be added"
    );
}

// -- Invariants ---------------------------------------------------------------

// Needed for speed-up and some vacuity issues
definition isIgnoredMethod_Invariant(method f) returns bool = (
    f.selector == sig:addValidators(uint256,uint32,bytes).selector ||
    f.selector == sig:pickNextValidatorsToDeposit(uint256).selector ||
    f.selector == sig:removeValidators(uint256, uint256[]).selector ||
    f.selector == sig:requestValidatorExits(uint256).selector
);


/// @title Checks that limit is not less than number of funded
function isValidlyFundedOperator(uint256 opIndex) returns bool {
    OperatorsV2.Operator operator = getOperator(opIndex);
    return operator.limit >= operator.funded;
}


/**
    @title Active operators are in a valid state
**/
invariant operatorsAreValidlyFunded(uint256 opIndex)
    isValidlyFundedOperator(opIndex)
    filtered {
        f -> !isIgnoredMethod_Invariant(f)
    }
    {
        preserved {
            require getOperatorsCount() < 2^5;
        }
    }

// -- Parametric vs invariant 1 ------------------------------------------------

// Needed for speed-up and some vacuity issues
definition isIgnoredMethod_PvsI(method f) returns bool = (
    f.selector == sig:addValidators(uint256,uint32,bytes).selector ||
    f.selector == sig:forceFundedValidatorKeysEventEmission(uint256).selector ||
    f.selector == sig:pickNextValidatorsToDeposit(uint256).selector ||
    f.selector == sig:removeValidators(uint256, uint256[]).selector ||
    f.selector == sig:requestValidatorExits(uint256).selector
);

rule badParametricRule(method f) filtered {
    f -> !(isIgnoredMethod_PvsI(f) || f.isView)
} {
    require getOperatorsCount() < 2^5;
    require getOperatorsCount() >= 1;  // Pre-condition

    env e;
    calldataarg args;
    f(e, args);

    assert getOperatorsCount() >= 1;
}


invariant goodInvariant()
    getOperatorsCount() >= 1
    filtered {
        f -> !isIgnoredMethod_PvsI(f)
    }
    {
        preserved {
            require getOperatorsCount() < 2^5;
        }
    }

// -- State machine ------------------------------------------------------------

/// @title Is operator in a valid state
function isValidOperatorState(uint256 opIndex) returns bool {
    uint32 keys;
    uint32 limit;
    uint32 funded;
    uint32 requestedExits;
    OperatorsV2.Operator operator = getOperator(opIndex);
    return (
        operator.keys >= operator.limit &&
        operator.limit >= operator.funded &&
        operator.funded >= operator.requestedExits &&
        opIndex < getOperatorsCount()
    );
}


/**
    @title Valid operator state
**/
invariant operatorIsInValidState(uint256 opIndex)
    isValidOperatorState(opIndex)
    filtered {
        f -> !isIgnoredMethod_Invariant(f)
    }
    {
        preserved {
            require getOperatorsCount() < 2^5;
        }
    }


/**
    @title Funded -> Exited validator state change rule
    Note - it is wrong in general to use the index to identify the validator, since it
    can be changed by remove validators. Using the key is preferred, but hard. It can be
    used for testing methods other than `removeValidators`.
**/
rule fundedToExitedValidatorStateChange(uint256 opIndex, uint256 valIndex, method f) {
    // Require that we be in a valid state
    requireInvariant operatorIsInValidState(opIndex);
    require getOperatorsCount() < 2^5;

    // Pre-condition
    require getValidatorStateByIndex(opIndex, valIndex) == 3;

    env e;
    calldataarg args;
    f(e, args);

    uint256 newState = getValidatorStateByIndex(opIndex, valIndex);

    assert newState == 3 || newState == 4, "Funded can only become Exited";
    // Add assertions - which methods can change the state?
}
