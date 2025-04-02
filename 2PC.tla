---- MODULE 2PC ----
EXTENDS Naturals
CONSTANT Sites
CONSTANT Decisions
CONSTANT CommitPhaseDecisions
CONSTANT TransactionStatuses
CONSTANT SiteTimeout
VARIABLE sentVotingRequests
VARIABLE receivedVotingRequests
VARIABLE sentVotingResponses
VARIABLE receivedVotingResponses
VARIABLE sentCommitDecisions
VARIABLE receivedCommitDecisions
VARIABLE coordinatorStatus
VARIABLE siteStatuses
VARIABLE votingPhaseComplete
VARIABLE commitPhaseComplete
VARIABLE sentAcks
VARIABLE receivedAcks
VARIABLE transactionStatus
VARIABLE siteTimeouts
vars == 
    <<
        sentVotingRequests, 
        receivedVotingRequests,
        sentVotingResponses,
        receivedVotingResponses,
        sentCommitDecisions,
        votingPhaseComplete,
        commitPhaseComplete,
        receivedCommitDecisions,
        coordinatorStatus,
        siteStatuses,
        sentAcks,
        receivedAcks,
        transactionStatus,
        siteTimeouts
    >>

TypeOK ==
    /\ sentVotingRequests \in SUBSET Sites
    /\ receivedVotingRequests \in SUBSET Sites
    /\ sentVotingResponses \in [Sites -> Decisions]
    /\ receivedVotingResponses \in [Sites -> Decisions]
    /\ sentCommitDecisions \in [Sites -> CommitPhaseDecisions]
    /\ receivedCommitDecisions \in [Sites -> CommitPhaseDecisions]
    /\ sentAcks \in SUBSET Sites
    /\ receivedAcks \in SUBSET Sites
    /\ coordinatorStatus \in BOOLEAN 
    /\ siteStatuses \in [Sites -> BOOLEAN]
    /\ votingPhaseComplete \in BOOLEAN
    /\ commitPhaseComplete \in BOOLEAN
    /\ transactionStatus \in TransactionStatuses
    /\ siteTimeouts \in [Sites -> Nat]

---------    

TryCompleteVotingPhase ==
    /\ votingPhaseComplete = FALSE
    /\ \A s \in Sites: receivedVotingResponses[s] # "Waiting"
    /\ votingPhaseComplete' = TRUE
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, commitPhaseComplete, receivedVotingResponses, coordinatorStatus, siteStatuses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>


SendRequest(s) ==
    /\ votingPhaseComplete = FALSE
    /\ coordinatorStatus = TRUE
    /\ \/ /\ siteStatuses[s] = TRUE
          /\ s \notin sentVotingRequests
          /\ sentVotingRequests' = sentVotingRequests \cup {s}
          /\ UNCHANGED <<receivedVotingRequests, sentVotingResponses, votingPhaseComplete, commitPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>
       \/ /\ siteStatuses[s] = FALSE
          /\ siteTimeouts' = [siteTimeouts EXCEPT ![s] = siteTimeouts[s] + 1]
          /\ siteTimeouts[s] \geq SiteTimeout => votingPhaseComplete' = TRUE
          /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, commitPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus>>

ReceiveRequest(s) ==
    /\ votingPhaseComplete = FALSE
    /\ \/ /\ siteStatuses[s] = TRUE
          /\ s \in sentVotingRequests
          /\ s \notin receivedVotingRequests
          /\ receivedVotingRequests' = receivedVotingRequests \cup {s}
          /\ UNCHANGED <<sentVotingRequests, sentVotingResponses, votingPhaseComplete, commitPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>
       \/ /\ siteStatuses[s] = FALSE
          /\ siteTimeouts' = [siteTimeouts EXCEPT ![s] = siteTimeouts[s] + 1]
          /\ siteTimeouts[s] \geq SiteTimeout => votingPhaseComplete' = TRUE
          /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, commitPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus>>

ProvideResponse(s) ==
    /\ votingPhaseComplete = FALSE
    /\ coordinatorStatus = TRUE
    /\ \/ /\ siteStatuses[s] = TRUE
          /\ s \in receivedVotingRequests
          /\ sentVotingResponses[s] = "Waiting"
          /\ \E d \in (Decisions \ {"Waiting"}) :
            sentVotingResponses' = [sentVotingResponses EXCEPT ![s] = d]
          /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>
       \/ /\ siteStatuses[s] = FALSE
          /\ siteTimeouts' = [siteTimeouts EXCEPT ![s] = siteTimeouts[s] + 1]
          /\ siteTimeouts[s] \geq SiteTimeout => votingPhaseComplete' = TRUE
          /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, commitPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus>>

ReceiveResponse(s) ==
    /\ votingPhaseComplete = FALSE
    /\ coordinatorStatus = TRUE
    /\ sentVotingResponses[s] # "Waiting"
    /\ receivedVotingResponses[s] = "Waiting"
    /\ receivedVotingResponses' = [receivedVotingResponses EXCEPT ![s] = sentVotingResponses[s]]
    /\ TryCompleteVotingPhase
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, sentVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

SendCommitDecision(s, d) ==
    /\ coordinatorStatus = TRUE
    /\ siteStatuses[s] = TRUE
    /\ sentCommitDecisions[s] = "Waiting"
    /\ sentCommitDecisions' = [sentCommitDecisions EXCEPT ![s] = d]
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, sentVotingResponses, receivedVotingResponses, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

ReceiveCommitDecision(s) ==
    /\ siteStatuses[s] = TRUE
    /\ sentCommitDecisions[s] # "Waiting"
    /\ receivedCommitDecisions[s] = "Waiting"
    /\ receivedCommitDecisions' = [receivedCommitDecisions EXCEPT ![s] = sentCommitDecisions[s]]
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, sentVotingResponses, receivedVotingResponses, sentCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

SendAck(s) ==
    /\ coordinatorStatus = TRUE
    /\ siteStatuses[s] = TRUE
    /\ receivedCommitDecisions[s] # "Waiting"
    /\ s \notin sentAcks
    /\ sentAcks' = sentAcks \cup {s}
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, sentVotingResponses, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, receivedAcks, transactionStatus, siteTimeouts>>

ReceiveAck(s) ==
    /\ coordinatorStatus = TRUE
    /\ s \in sentAcks
    /\ s \notin receivedAcks
    /\ receivedAcks' = receivedAcks \cup {s}
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, sentVotingResponses, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, transactionStatus>>

FailCoordinator ==
    /\ commitPhaseComplete = FALSE
    /\ coordinatorStatus' = FALSE
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, receivedVotingResponses, commitPhaseComplete, votingPhaseComplete, siteStatuses, sentCommitDecisions, receivedCommitDecisions, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

RecoverCoordinator ==
    /\ coordinatorStatus = FALSE
    /\ coordinatorStatus' = TRUE
    /\ \/ /\ votingPhaseComplete = FALSE
          /\ votingPhaseComplete' = TRUE
          /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, receivedVotingResponses, commitPhaseComplete, siteStatuses, sentCommitDecisions, receivedCommitDecisions, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>
       \/ /\ votingPhaseComplete = TRUE
          /\ commitPhaseComplete = FALSE
          /\ \/ /\ \E s \in Sites: sentCommitDecisions[s] = "Waiting"
                /\ LET s == CHOOSE t \in Sites: sentCommitDecisions[t] = "Waiting"
                    IN \/ /\ \A site \in Sites: receivedVotingResponses[site] = "Yes"
                          /\ sentCommitDecisions' = [sentCommitDecisions EXCEPT ![s] = "Commit"]
                          /\ receivedCommitDecisions' = [receivedCommitDecisions EXCEPT ![s] = "Commit"]
                       \/ /\ \E site \in Sites: receivedVotingResponses[site] # "Yes"
                          /\ sentCommitDecisions' = [sentCommitDecisions EXCEPT ![s] = "Abort"]
                          /\ receivedCommitDecisions' = [receivedCommitDecisions EXCEPT ![s] = "Abort"]   
                       /\ sentAcks' = sentAcks \cup {s}
                       /\ receivedAcks' = receivedAcks \cup {s}
                /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, receivedVotingResponses, votingPhaseComplete, commitPhaseComplete, siteStatuses, siteStatuses, transactionStatus, siteTimeouts>>
             \/ /\ \A s \in Sites: receivedCommitDecisions[s] # "Waiting"
                /\ commitPhaseComplete' = TRUE
                /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, receivedVotingResponses, votingPhaseComplete, siteStatuses, sentCommitDecisions, receivedCommitDecisions, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

FailSite(s) ==
    /\ commitPhaseComplete = FALSE
    /\ siteStatuses[s] = TRUE
    /\ siteStatuses' = [siteStatuses EXCEPT ![s] = FALSE]
    /\ receivedVotingRequests' = receivedVotingRequests \ {s}
    /\ UNCHANGED <<sentVotingRequests, sentVotingResponses, commitPhaseComplete, votingPhaseComplete, receivedVotingResponses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

RecoverSite(s) ==
    /\ siteStatuses[s] = FALSE
    /\ siteStatuses' = [siteStatuses EXCEPT ![s] = TRUE]
    /\ \/ /\ votingPhaseComplete = FALSE
          /\ s \in sentVotingRequests
          /\ \/ /\ siteTimeouts[s] \geq SiteTimeout 
                /\ votingPhaseComplete' = TRUE
                /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests,sentVotingResponses, commitPhaseComplete, receivedVotingResponses, receivedCommitDecisions, sentCommitDecisions, coordinatorStatus, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>  
             \/ /\ siteTimeouts[s] < SiteTimeout 
                /\ receivedVotingRequests' = receivedVotingRequests \cup {s}
                /\ siteTimeouts' = [siteTimeouts EXCEPT ![s] = siteTimeouts[s] + 1]
                /\ UNCHANGED <<sentVotingRequests,sentVotingResponses, votingPhaseComplete, commitPhaseComplete, receivedVotingResponses, receivedCommitDecisions, sentCommitDecisions, coordinatorStatus, sentAcks, receivedAcks, transactionStatus>>      
       \/ /\ votingPhaseComplete = TRUE
          /\ commitPhaseComplete = FALSE
          /\ receivedCommitDecisions[s] = "Waiting"
          /\ \/ /\ sentCommitDecisions[s] = "Waiting"
                /\ \/ /\ \E t \in Sites: receivedVotingResponses[t] # "Yes"
                      /\ sentCommitDecisions' = [sentCommitDecisions EXCEPT ![s] = "Abort"]
                      /\ receivedCommitDecisions' = [receivedCommitDecisions EXCEPT ![s] = "Abort"]
                   \/ /\ \A t \in Sites: receivedVotingResponses[t] = "Yes"
                      /\ sentCommitDecisions' = [sentCommitDecisions EXCEPT ![s] = "Commit"]
                      /\ receivedCommitDecisions' = [receivedCommitDecisions EXCEPT ![s] = "Commit"]   
             \/ /\ sentCommitDecisions[s] # "Waiting"
                /\ receivedCommitDecisions' = [receivedCommitDecisions EXCEPT ![s] = sentCommitDecisions[s]]   
          /\ sentAcks' = sentAcks \cup {s}
          /\ receivedAcks' = receivedAcks \cup {s}
          /\ UNCHANGED <<receivedVotingRequests, sentVotingRequests, sentVotingResponses, commitPhaseComplete, votingPhaseComplete, receivedVotingResponses, sentCommitDecisions, coordinatorStatus, transactionStatus, siteTimeouts>>

PropagateCommitOrAbort(d) ==
    \E s \in Sites:
        \/ SendCommitDecision(s, d)
        \/ ReceiveCommitDecision(s)
        \/ SendAck(s)
        \/ ReceiveAck(s)
        \/ FailSite(s)
        \/ RecoverSite(s)
        \/ FailCoordinator
        \/ RecoverCoordinator

CommitOrAbort ==
    /\ votingPhaseComplete = TRUE
    /\ \/ /\ \E s \in Sites: receivedVotingResponses[s] # "Yes"
          /\ PropagateCommitOrAbort("Abort")
       \/ /\ \A s \in Sites: receivedVotingResponses[s] = "Yes"
          /\ PropagateCommitOrAbort("Commit")
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, votingPhaseComplete, commitPhaseComplete, sentVotingResponses, receivedVotingResponses, transactionStatus, siteTimeouts>>


CompleteCommitPhase ==
    /\ votingPhaseComplete = TRUE
    /\ commitPhaseComplete = FALSE
    /\ receivedAcks = Sites
    /\ commitPhaseComplete' = TRUE
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, votingPhaseComplete, receivedVotingResponses, coordinatorStatus, siteStatuses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, transactionStatus, siteTimeouts>>

CompleteTransaction ==
    /\ votingPhaseComplete = TRUE
    /\ commitPhaseComplete = TRUE
    /\ transactionStatus = "InProgress"
    /\ \/ /\ \A s \in Sites: receivedCommitDecisions[s] = "Abort"
          /\ transactionStatus' = "Aborted"
       \/ /\ \A s \in Sites: receivedCommitDecisions[s] = "Commit"
          /\ transactionStatus' = "Commited"
    /\ UNCHANGED <<sentVotingRequests, receivedVotingRequests, sentVotingResponses, votingPhaseComplete, commitPhaseComplete, receivedVotingResponses, coordinatorStatus, siteStatuses, sentCommitDecisions, receivedCommitDecisions, coordinatorStatus, siteStatuses, sentAcks, receivedAcks, siteTimeouts>>

Complete ==
    /\ transactionStatus # "InProgress"
    /\ UNCHANGED vars

CollectVotes ==
    /\ votingPhaseComplete = FALSE
    /\ \E s \in Sites:
        \/ SendRequest(s)
        \/ ReceiveRequest(s)
        \/ ProvideResponse(s)
        \/ ReceiveResponse(s)
        \/ FailSite(s)
        \/ RecoverSite(s)
        \/ FailCoordinator
        \/ RecoverCoordinator
    /\ UNCHANGED <<sentCommitDecisions, receivedCommitDecisions, receivedAcks, transactionStatus, votingPhaseComplete, commitPhaseComplete, sentAcks>>

---------

Init ==
    /\ sentVotingRequests = {}
    /\ receivedVotingRequests = {}
    /\ sentVotingResponses = [s \in Sites |-> "Waiting"]
    /\ receivedVotingResponses = [s \in Sites |-> "Waiting"]
    /\ sentCommitDecisions = [s \in Sites |-> "Waiting"]
    /\ receivedCommitDecisions = [s \in Sites |-> "Waiting"]
    /\ coordinatorStatus = TRUE
    /\ siteStatuses = [s \in Sites |-> TRUE]
    /\ sentAcks = {}
    /\ receivedAcks = {}
    /\ votingPhaseComplete = FALSE
    /\ commitPhaseComplete = FALSE
    /\ transactionStatus = "InProgress"
    /\ siteTimeouts = [s \in Sites |-> 0]

Next ==
    \/ CollectVotes
    \/ FailCoordinator
    \/ RecoverCoordinator
    \/ \E s \in Sites:
        \/ FailSite(s)
        \/ RecoverSite(s)
    \/ CommitOrAbort
    \/ CompleteCommitPhase
    \/ CompleteTransaction
    \/ Complete

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------

\* Invariants

SiteReceivedRequestSetIsASubsetOfSentRequestSet ==
    receivedVotingRequests \subseteq sentVotingRequests

ReceivedAckSetIsASubsetOfSentAckSet ==
    receivedAcks \subseteq sentAcks

\* Properties

EventuallyVotingPhaseCompletes ==
     <>[] (votingPhaseComplete = TRUE)

EventuallyCommitPhaseCompletes ==
     <>[] (commitPhaseComplete = TRUE)

EventuallyTransactionCompletes ==
    <> (transactionStatus # "InProgress")

TransactionAbortedIfAllCommitDecisionsAreAbort ==
    <>(\A s \in Sites: sentCommitDecisions[s] = "Abort") => 
        <> (transactionStatus = "Aborted")

TransactionAbortedIfCoordinatorFailsBeforeReceivingAllVotes ==
    <>(coordinatorStatus = FALSE /\ votingPhaseComplete = FALSE /\ \E s \in Sites: receivedVotingResponses[s] # "Yes") =>
        <> (transactionStatus = "Aborted")

TransactionCommitedIfAllCommitDecisionsAreCommit ==
    <>(\A s \in Sites: sentCommitDecisions[s] = "Commit") => 
        <> (transactionStatus = "Commited")

CommitDecisionsAreNotConflicting ==
    \/ <>(\E s \in Sites: sentCommitDecisions[s] = "Commit") =>
         <>[](\A s \in Sites: sentCommitDecisions[s] = "Commit")
    \/ <>(\E s \in Sites: sentCommitDecisions[s] = "Abort") =>
         <>[](\A s \in Sites: sentCommitDecisions[s] = "Abort")   

CommitDecisionsCorrespondToVotes ==
    \/ <>(\A s \in Sites: receivedVotingResponses[s] = "Yes") =>
         <>(\A s \in Sites: sentCommitDecisions[s] = "Commit")
    \/ <>(\E s \in Sites: receivedVotingResponses[s] # "Yes") =>
         <>(\A s \in Sites: sentCommitDecisions[s] = "Abort")
====