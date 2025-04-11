---- MODULE 2PC_ref ----
EXTENDS 2PC 

votingPhaseConsensusDef == 
    IF votingPhaseComplete 
        THEN IF \E s \in Sites: receivedVotingResponses[s] = "Waiting" 
            THEN "NotAvailable"
        ELSE IF \A s \in Sites: receivedVotingResponses[s] = "Yes" 
            THEN "Yes"
        ELSE "No"
    ELSE "NotAvailable"

failureDuringVotingPhaseDef == 
    \/ /\ coordinatorStatus = FALSE 
       /\ votingPhaseComplete = FALSE
    \/ /\ votingPhaseComplete = TRUE
       /\ \E s \in Sites: receivedVotingResponses[s] = "Waiting" 
       

commitPhaseDecisionDef == 
    IF commitPhaseComplete = FALSE 
        THEN "Waiting"
    ELSE IF \E s \in Sites: receivedCommitDecisions[s] # "Commit" 
        THEN "Abort"
    ELSE "Commit"

Abs == INSTANCE 2PC_abs
        WITH
            VotingPhaseConsensuses <- Decisions,
            failureDuringVotingPhase <- failureDuringVotingPhaseDef, 
            votingPhaseConsensus <- votingPhaseConsensusDef,
            transactionStatus <- transactionStatus,
            commitPhaseDecision <- commitPhaseDecisionDef

Refinement == Abs!Spec

THEOREM Spec => Refinement
PROOF OBVIOUS 

====