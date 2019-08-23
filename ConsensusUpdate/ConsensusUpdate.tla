-------------------------- MODULE ConsensusUpdate --------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS
    Names, \* a set
    Participants, \* An array of participants, in their order in the state channel
    Behaviours,   \* [p \in Participants: AllowedBehaviours]
    NULL

ParticipantIndices == DOMAIN Participants
NumParticipants == Len(Participants)
Types == [
    WAITING    |-> "WAITING",
    SENT       |-> "SENT",
    SUCCESS    |-> "SUCCESS",
    ABORTED    |-> "ABORTED", \* If someone veto's
    TERMINATED |-> "TERMINATED" \* If someone sleeps, the channel is terminated
]
Status == [
  OK      |-> "OK",
  ABORT   |-> "ABORT",
  SUCCESS |-> "SUCCESS"
]
AllowedBehaviours == [
  VOTE         |-> "VOTE",
  VETO         |-> "VETO",
  SEND_INVALID |-> "SEND_INVALID",
  SLEEP        |-> "SLEEP"
]
ChallengeStatus == [
  CLEARED |-> "CLEARED",
  ACTIVE  |-> "ACTIVE",
  EXPIRED |-> "EXPIRED"
]

Range(f) == { f[x] : x \in DOMAIN f }
Running(state) == state.type \in { Types.WAITING, Types.SENT }
Terminated(state) == ~Running(state)
StartingTurnNumber == 1

ASSUME
  /\ Len(Participants) > 1
  /\ \A p \in ParticipantIndices: Behaviours[p] \in Range(AllowedBehaviours)
            
(* --algorithm consensus_update
\* This is Pluscal (Pascal for TLA+)

variables msgs = [p \in Names |-> {}],
          challenge = [turnNumber |-> 0, status |-> ChallengeStatus.CLEARED, votesRequired |-> 0]

define
\* Arrays are 1-indexed, while the % operator returns a number between 0 and NumParticipants.
\* This explains the following slightly complicated expression
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
currentlyOurTurn(state) ==
    /\ state.type = Types.WAITING
    /\ state.ourIndex = mover(state.turnNumber)
becomesOurTurn(state, msg) ==
   /\ state.type = Types.WAITING
   /\ msg.status = Status.OK
   /\ state.ourIndex = mover(msg.turnNumber)
challengeIsPresent == challenge.status # ChallengeStatus.CLEARED

target(turnNumber) == Participants[mover(turnNumber)]
end define;

macro broadcastMsg(m, sender)
begin
msgs := [recipient \in Names |-> IF recipient = sender THEN msgs[recipient] ELSE msgs[recipient] \cup {m}];
end macro;

macro sendVote(turnNumber, votesRequired, me)
begin
assert votesRequired > 0;
state := [
    type |-> Types.SENT,
    turnNumber |-> turnNumber,
    votesRequired |-> votesRequired,
    ourIndex   |-> state.ourIndex
];
broadcastMsg([
    turnNumber      |-> state.turnNumber,
    votesRequired   |-> votesRequired,
    status          |-> Status.OK
], me)
end macro;

macro returnSuccess(turnNumber, me)
begin
state :=     [ type  |-> Types.SUCCESS,  turnNumber |-> turnNumber] @@ state;
broadcastMsg([status |-> Status.SUCCESS, turnNumber |-> turnNumber], me)
end macro;

macro abort(turnNumber, me)
begin
state := [
    type |-> Types.FAILURE,
    turnNumber |-> turnNumber
] @@ state;
broadcastMsg([
    status |-> Status.ABORT,
    turnNunber |-> turnNumber
], me);
end macro;
 
macro vote(turnNumber, votesRequired)
begin
if votesRequired = 0 then returnSuccess(turnNumber+1, me)
else sendVote(turnNumber+1, votesRequired, me)
end if; end macro;

macro waitForUpdate(turnNumber, me)
begin
state := [
    turnNumber    |-> msg.turnNumber,
    votesRequired |-> msg.votesRequired,
    type          |-> Types.WAITING,
    ourIndex      |-> state.ourIndex
];
msgs[me] := msgs[me] \ {msg};
end macro;

macro takeAction(turnNumber, votesRequired, me)
begin
    if state.type = Types.WAITING then
        if Behaviours[self] = AllowedBehaviours.VOTE then
            vote(turnNumber, votesRequired);
        elsif Behaviours[self] = AllowedBehaviours.VETO then
            abort(turnNumber, me);
        elsif Behaviours[self] = AllowedBehaviours.SLEEP then skip;
        else assert FALSE
        end if;
    elsif state.type = Types.SENT then abort(turnNumber, me);
    else assert FALSE
    end if;
end macro;

macro terminate(turnNumber)
begin
state := [
    type |-> Types.TERMINATED,
    turnNumber |-> turnNumber
] @@ state;
end macro;

macro forceMove(turnNumber, votesRequired)
begin
challenge := [
  turnNumber    |-> turnNumber,
  status        |-> ChallengeStatus.ACTIVE,
  votesRequired |-> votesRequired
];
broadcastMsg([
    turnNumber    |-> turnNumber,
    votesRequired |-> votesRequired,
    status        |-> Status.OK
], NULL)

end macro;

macro processChallenge()
begin skip; end macro;

macro respondToChallenge()
begin
skip;
end macro;

fair process adjudicator = 0
begin
(****************************************************************************
This process expires challenges.
****************************************************************************)
HandleChallenge:
while challenge.status # ChallengeStatus.EXPIRED
do
    await challenge.status = ChallengeStatus.ACTIVE;
    ExpireChallenge:
        challenge := [ status |-> ChallengeStatus.EXPIRED ] @@ challenge;
        broadcastMsg([ status |-> ChallengeStatus.EXPIRED, turnNumber |-> challenge.turnNumber], NULL)
end while;
end process;

fair process consensusUpdate \in ParticipantIndices \* This set is {1, 2} in a 2-party channel
(***************************************************************************
A consensusUpdate process is said to be correct if it takes the "VOTE" or "VETO" action.
In the nitro protocol framework, this corresponds to sending a valid commitment.

Other actions that a process can take are: 
The consensusUpdate protocol should have the following properties:
1. The protocol eventually terminates in all correct processes.
2. If all processes are correct, then either
   A. All processes terminate correctly; or
   B. The channel terminates on-chain via an expired challenge.
3. If at least one process is incorrect, then the protocol never terminates successfully in any correct process


 ***************************************************************************)
variables
  state = [
    turnNumber |-> StartingTurnNumber,
    votesRequired |-> 0,
    ourIndex |-> self,
    type |-> Types.WAITING
  ],
  \* The following two variables are just "helper" variables
  me = Participants[self],
  msg = NULL

begin
  ReachConsensus:
    while Running(state) do
(****************************************************************************
   Each participant either
  A. sends a message if it's currently safe to do so, or else
  B.
    i)   reads a message for the participant
    ii)  updates their state accordingly and sends a message if it's
         then safe
    iii) removes the message from their inbox.
  C. calls forceMove, triggering a challenge

In the case B, these three actions are currently assumed to be atomic.
****************************************************************************)
        if Behaviours[self] = AllowedBehaviours.SLEEP then skip;
        elsif currentlyOurTurn(state) then takeAction(state.turnNumber, NumParticipants - 1, me);
        else 
            either
            \* My wallet should have some timeout after which it plays a forceMove
            \* This allows my wallet to ensure that the consensusUpdate protocol eventually terminates
            ForceMove:
                if /\ ~currentlyOurTurn(state)
                   /\ ~challengeIsPresent
                then
                    assert challenge.status = ChallengeStatus.CLEARED;
                    forceMove(state.turnNumber, state.votesRequired);
                    WaitForChallengeResponse:
                        await challenge.status # ChallengeStatus.ACTIVE;
                        if    challenge.status = ChallengeStatus.EXPIRED then terminate(challenge.turnNumber);
                        else assert FALSE;
                        end if;
                end if;
             or
                \* My wallet noticed an event (a challenge or message) and responds accordingly                
                ReadMessage: with m \in msgs[me] do msg := m end with;
                ProcessMessage:
                    if msg.status = Status.OK then
                        if msg.turnNumber > state.turnNumber then
                            if becomesOurTurn(state, msg) then takeAction(msg.turnNumber, msg.votesRequired - 1, me);
                            else waitForUpdate(msg, me);
                            end if;
                        else
                            \* Optional logging statement:
                            \* print(<<"Message ignored: ", msg, challenge.status>>);
                            skip;
                        end if;
                    elsif msg.status = Status.ABORT   then abort(state.turnNumber, me)
                    elsif msg.status = Status.SUCCESS then returnSuccess(msg.turnNumber, me)
                    elsif msg.status = ChallengeStatus.EXPIRED then terminate(msg.turnNumber)
                    else print msg; assert FALSE;
                    end if;
                RemoveMessage:
                    assert msg # NULL;
                    msgs[me] := msgs[me] \ {msg};
                    msg := NULL;
                        
            end either;
        end if;
    end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES msgs, challenge, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
currentlyOurTurn(state) ==
    /\ state.type = Types.WAITING
    /\ state.ourIndex = mover(state.turnNumber)
becomesOurTurn(state, msg) ==
   /\ state.type = Types.WAITING
   /\ msg.status = Status.OK
   /\ state.ourIndex = mover(msg.turnNumber)
challengeIsPresent == challenge.status # ChallengeStatus.CLEARED

target(turnNumber) == Participants[mover(turnNumber)]

VARIABLES state, me, msg

vars == << msgs, challenge, pc, state, me, msg >>

ProcSet == {0} \cup (ParticipantIndices)

Init == (* Global variables *)
        /\ msgs = [p \in Names |-> {}]
        /\ challenge = [turnNumber |-> 0, status |-> ChallengeStatus.CLEARED, votesRequired |-> 0]
        (* Process consensusUpdate *)
        /\ state = [self \in ParticipantIndices |->         [
                                                      turnNumber |-> StartingTurnNumber,
                                                      votesRequired |-> 0,
                                                      ourIndex |-> self,
                                                      type |-> Types.WAITING
                                                    ]]
        /\ me = [self \in ParticipantIndices |-> Participants[self]]
        /\ msg = [self \in ParticipantIndices |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "HandleChallenge"
                                        [] self \in ParticipantIndices -> "ReachConsensus"]

HandleChallenge == /\ pc[0] = "HandleChallenge"
                   /\ IF challenge.status # ChallengeStatus.EXPIRED
                         THEN /\ challenge.status = ChallengeStatus.ACTIVE
                              /\ pc' = [pc EXCEPT ![0] = "ExpireChallenge"]
                         ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << msgs, challenge, state, me, msg >>

ExpireChallenge == /\ pc[0] = "ExpireChallenge"
                   /\ challenge' = [ status |-> ChallengeStatus.EXPIRED ] @@ challenge
                   /\ msgs' = [recipient \in Names |-> IF recipient = NULL THEN msgs[recipient] ELSE msgs[recipient] \cup {([ status |-> ChallengeStatus.EXPIRED, turnNumber |-> challenge'.turnNumber])}]
                   /\ pc' = [pc EXCEPT ![0] = "HandleChallenge"]
                   /\ UNCHANGED << state, me, msg >>

adjudicator == HandleChallenge \/ ExpireChallenge

ReachConsensus(self) == /\ pc[self] = "ReachConsensus"
                        /\ IF Running(state[self])
                              THEN /\ IF Behaviours[self] = AllowedBehaviours.SLEEP
                                         THEN /\ TRUE
                                              /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                              /\ UNCHANGED << msgs, state >>
                                         ELSE /\ IF currentlyOurTurn(state[self])
                                                    THEN /\ IF state[self].type = Types.WAITING
                                                               THEN /\ IF Behaviours[self] = AllowedBehaviours.VOTE
                                                                          THEN /\ IF (NumParticipants - 1) = 0
                                                                                     THEN /\ state' = [state EXCEPT ![self] = [ type  |-> Types.SUCCESS,  turnNumber |-> ((state[self].turnNumber)+1)] @@ state[self]]
                                                                                          /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS, turnNumber |-> ((state'[self].turnNumber)+1)])}]
                                                                                     ELSE /\ Assert((NumParticipants - 1) > 0, 
                                                                                                    "Failure of assertion at line 73, column 1 of macro called at line 225, column 44.")
                                                                                          /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                  type |-> Types.SENT,
                                                                                                                                  turnNumber |-> ((state[self].turnNumber)+1),
                                                                                                                                  votesRequired |-> (NumParticipants - 1),
                                                                                                                                  ourIndex   |-> state[self].ourIndex
                                                                                                                              ]]
                                                                                          /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                                                                         turnNumber      |-> state'[self].turnNumber,
                                                                                                         votesRequired   |-> (NumParticipants - 1),
                                                                                                         status          |-> Status.OK
                                                                                                     ])}]
                                                                          ELSE /\ IF Behaviours[self] = AllowedBehaviours.VETO
                                                                                     THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                  type |-> Types.FAILURE,
                                                                                                                                  turnNumber |-> (state[self].turnNumber)
                                                                                                                              ] @@ state[self]]
                                                                                          /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                                                                         status |-> Status.ABORT,
                                                                                                         turnNunber |-> (state'[self].turnNumber)
                                                                                                     ])}]
                                                                                     ELSE /\ IF Behaviours[self] = AllowedBehaviours.SLEEP
                                                                                                THEN /\ TRUE
                                                                                                ELSE /\ Assert(FALSE, 
                                                                                                               "Failure of assertion at line 130, column 14 of macro called at line 225, column 44.")
                                                                                          /\ UNCHANGED << msgs, 
                                                                                                          state >>
                                                               ELSE /\ IF state[self].type = Types.SENT
                                                                          THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                                       type |-> Types.FAILURE,
                                                                                                                       turnNumber |-> (state[self].turnNumber)
                                                                                                                   ] @@ state[self]]
                                                                               /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                                                              status |-> Status.ABORT,
                                                                                              turnNunber |-> (state'[self].turnNumber)
                                                                                          ])}]
                                                                          ELSE /\ Assert(FALSE, 
                                                                                         "Failure of assertion at line 133, column 10 of macro called at line 225, column 44.")
                                                                               /\ UNCHANGED << msgs, 
                                                                                               state >>
                                                         /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                                    ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "ForceMove"]
                                                            \/ /\ pc' = [pc EXCEPT ![self] = "ReadMessage"]
                                                         /\ UNCHANGED << msgs, 
                                                                         state >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << msgs, state >>
                        /\ UNCHANGED << challenge, me, msg >>

ForceMove(self) == /\ pc[self] = "ForceMove"
                   /\ IF /\ ~currentlyOurTurn(state[self])
                         /\ ~challengeIsPresent
                         THEN /\ Assert(challenge.status = ChallengeStatus.CLEARED, 
                                        "Failure of assertion at line 234, column 21.")
                              /\ challenge' =              [
                                                turnNumber    |-> (state[self].turnNumber),
                                                status        |-> ChallengeStatus.ACTIVE,
                                                votesRequired |-> (state[self].votesRequired)
                                              ]
                              /\ msgs' = [recipient \in Names |-> IF recipient = NULL THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                             turnNumber    |-> (state[self].turnNumber),
                                             votesRequired |-> (state[self].votesRequired),
                                             status        |-> Status.OK
                                         ])}]
                              /\ pc' = [pc EXCEPT ![self] = "WaitForChallengeResponse"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                              /\ UNCHANGED << msgs, challenge >>
                   /\ UNCHANGED << state, me, msg >>

WaitForChallengeResponse(self) == /\ pc[self] = "WaitForChallengeResponse"
                                  /\ challenge.status # ChallengeStatus.ACTIVE
                                  /\ IF challenge.status = ChallengeStatus.EXPIRED
                                        THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                     type |-> Types.TERMINATED,
                                                                                     turnNumber |-> (challenge.turnNumber)
                                                                                 ] @@ state[self]]
                                        ELSE /\ Assert(FALSE, 
                                                       "Failure of assertion at line 239, column 30.")
                                             /\ state' = state
                                  /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                  /\ UNCHANGED << msgs, challenge, me, msg >>

ReadMessage(self) == /\ pc[self] = "ReadMessage"
                     /\ \E m \in msgs[me[self]]:
                          msg' = [msg EXCEPT ![self] = m]
                     /\ pc' = [pc EXCEPT ![self] = "ProcessMessage"]
                     /\ UNCHANGED << msgs, challenge, state, me >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF msg[self].status = Status.OK
                              THEN /\ IF msg[self].turnNumber > state[self].turnNumber
                                         THEN /\ IF becomesOurTurn(state[self], msg[self])
                                                    THEN /\ IF state[self].type = Types.WAITING
                                                               THEN /\ IF Behaviours[self] = AllowedBehaviours.VOTE
                                                                          THEN /\ IF (msg[self].votesRequired - 1) = 0
                                                                                     THEN /\ state' = [state EXCEPT ![self] = [ type  |-> Types.SUCCESS,  turnNumber |-> ((msg[self].turnNumber)+1)] @@ state[self]]
                                                                                          /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS, turnNumber |-> ((msg[self].turnNumber)+1)])}]
                                                                                     ELSE /\ Assert((msg[self].votesRequired - 1) > 0, 
                                                                                                    "Failure of assertion at line 73, column 1 of macro called at line 248, column 64.")
                                                                                          /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                  type |-> Types.SENT,
                                                                                                                                  turnNumber |-> ((msg[self].turnNumber)+1),
                                                                                                                                  votesRequired |-> (msg[self].votesRequired - 1),
                                                                                                                                  ourIndex   |-> state[self].ourIndex
                                                                                                                              ]]
                                                                                          /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                                                                         turnNumber      |-> state'[self].turnNumber,
                                                                                                         votesRequired   |-> (msg[self].votesRequired - 1),
                                                                                                         status          |-> Status.OK
                                                                                                     ])}]
                                                                          ELSE /\ IF Behaviours[self] = AllowedBehaviours.VETO
                                                                                     THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                  type |-> Types.FAILURE,
                                                                                                                                  turnNumber |-> (msg[self].turnNumber)
                                                                                                                              ] @@ state[self]]
                                                                                          /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                                                                         status |-> Status.ABORT,
                                                                                                         turnNunber |-> (msg[self].turnNumber)
                                                                                                     ])}]
                                                                                     ELSE /\ IF Behaviours[self] = AllowedBehaviours.SLEEP
                                                                                                THEN /\ TRUE
                                                                                                ELSE /\ Assert(FALSE, 
                                                                                                               "Failure of assertion at line 130, column 14 of macro called at line 248, column 64.")
                                                                                          /\ UNCHANGED << msgs, 
                                                                                                          state >>
                                                               ELSE /\ IF state[self].type = Types.SENT
                                                                          THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                                       type |-> Types.FAILURE,
                                                                                                                       turnNumber |-> (msg[self].turnNumber)
                                                                                                                   ] @@ state[self]]
                                                                               /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                                                              status |-> Status.ABORT,
                                                                                              turnNunber |-> (msg[self].turnNumber)
                                                                                          ])}]
                                                                          ELSE /\ Assert(FALSE, 
                                                                                         "Failure of assertion at line 133, column 10 of macro called at line 248, column 64.")
                                                                               /\ UNCHANGED << msgs, 
                                                                                               state >>
                                                    ELSE /\ state' = [state EXCEPT ![self] =          [
                                                                                                 turnNumber    |-> msg[self].turnNumber,
                                                                                                 votesRequired |-> msg[self].votesRequired,
                                                                                                 type          |-> Types.WAITING,
                                                                                                 ourIndex      |-> state[self].ourIndex
                                                                                             ]]
                                                         /\ msgs' = [msgs EXCEPT ![me[self]] = msgs[me[self]] \ {msg[self]}]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << msgs, state >>
                              ELSE /\ IF msg[self].status = Status.ABORT
                                         THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                      type |-> Types.FAILURE,
                                                                                      turnNumber |-> (state[self].turnNumber)
                                                                                  ] @@ state[self]]
                                              /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(             [
                                                             status |-> Status.ABORT,
                                                             turnNunber |-> (state'[self].turnNumber)
                                                         ])}]
                                         ELSE /\ IF msg[self].status = Status.SUCCESS
                                                    THEN /\ state' = [state EXCEPT ![self] = [ type  |-> Types.SUCCESS,  turnNumber |-> (msg[self].turnNumber)] @@ state[self]]
                                                         /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS, turnNumber |-> (msg[self].turnNumber)])}]
                                                    ELSE /\ IF msg[self].status = ChallengeStatus.EXPIRED
                                                               THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                            type |-> Types.TERMINATED,
                                                                                                            turnNumber |-> (msg[self].turnNumber)
                                                                                                        ] @@ state[self]]
                                                               ELSE /\ PrintT(msg[self])
                                                                    /\ Assert(FALSE, 
                                                                              "Failure of assertion at line 259, column 37.")
                                                                    /\ state' = state
                                                         /\ msgs' = msgs
                        /\ pc' = [pc EXCEPT ![self] = "RemoveMessage"]
                        /\ UNCHANGED << challenge, me, msg >>

RemoveMessage(self) == /\ pc[self] = "RemoveMessage"
                       /\ Assert(msg[self] # NULL, 
                                 "Failure of assertion at line 262, column 21.")
                       /\ msgs' = [msgs EXCEPT ![me[self]] = msgs[me[self]] \ {msg[self]}]
                       /\ msg' = [msg EXCEPT ![self] = NULL]
                       /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                       /\ UNCHANGED << challenge, state, me >>

consensusUpdate(self) == ReachConsensus(self) \/ ForceMove(self)
                            \/ WaitForChallengeResponse(self)
                            \/ ReadMessage(self) \/ ProcessMessage(self)
                            \/ RemoveMessage(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == adjudicator
           \/ (\E self \in ParticipantIndices: consensusUpdate(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ \A self \in ParticipantIndices : WF_vars(consensusUpdate(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
AllowedMessages ==
  [
    turnNumber: AllowedTurnNumbers,
    votesRequired : 0..(NumParticipants - 1),
    status: { Status.OK }
  ] \cup [
    status: { Status.ABORT, Status.SUCCESS },
    turnNumber: AllowedTurnNumbers
  ] \cup [
    status: { ChallengeStatus.EXPIRED },
    turnNumber: AllowedTurnNumbers
  ]
AllowedChallenges ==
  [
    turnNumber: AllowedTurnNumbers,
    status: Range(ChallengeStatus),
    votesRequired: 0..(NumParticipants - 1)
  ]
AllowedStates == [
    turnNumber: AllowedTurnNumbers,
    ourIndex: ParticipantIndices,
    votesRequired: 0..(NumParticipants - 1),
    type: Range(Types)
]

\* Safety properties

TypeOK ==
  /\ state \in [ParticipantIndices -> AllowedStates]
  /\ \A p \in Names : \A m \in msgs[p] : m \in AllowedMessages
  /\ challenge \in AllowedChallenges

\* TODO: Get TurnNumberDoesNotDecrease and StaysTerminated
\* For some reason, state[p].turnNumber' is not valid
TurnNumberDoesNotDecrease ==
  /\ \A p \in ParticipantIndices: state[p].turnNumber' >= state[p].turnNumber

\* Once a process has terminated, its state does not change.
StaysTerminated == \A p \in ParticipantIndices: (Terminated(state[p]) => (state'[p] = state[p]))
  
\* Liveness properties
ProtocolTerminatesWhenChallengeDoesNotExpire == 
    \/ <>[]( /\ challenge.status = ChallengeStatus.EXPIRED
             /\ \E p \in ParticipantIndices: state[p].type = Types.TERMINATED)
    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.SUCCESS
                                          /\ state[p].turnNumber = StartingTurnNumber + NumParticipants))
    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.ABORTED
                                          /\ state[p].turnNumber = state[1].turnNumber))
    
\* Message inboxes should eventually be empty
MessagesAreRead == <>[](msgs = [p \in ParticipantIndices |-> {}])

=============================================================================
\* Modification History
\* Last modified Fri Aug 23 09:41:15 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
