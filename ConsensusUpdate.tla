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
    FAILURE    |-> "FAILURE",
    TERMINATED |-> "TERMIATED"
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

variables msgs = [p \in Names |-> {}],
          challenge = NULL

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

someoneIsBlocking(idx) == \E p \in idx..NumParticipants : Behaviours[p] = AllowedBehaviours.SLEEP

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
    turnNumber |-> msg.turnNumber,
    type       |-> Types.WAITING,
    ourIndex   |-> state.ourIndex
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

macro forceMove(turnNumber)
begin
assert challenge = NULL;
challenge := [
  turnNumber |-> turnNumber,
  status     |-> ChallengeStatus.ACTIVE
];
end macro;

macro processChallenge()
begin skip; end macro;

macro respondToChallenge()
begin
skip;
end macro;

fair process consensusUpdate \in ParticipantIndices
(***************************************************************************
A consensusUpdate process is said to be correct if it takes the "VOTE" or "VETO" action.
In the nitro protocol framework, this corresponds to sending a valid commitment.

Other actions that a process can take are:
SEND_INVALID: the process sends an invalid commitment. In this case, the process thinks it has furthered
SLEEP: the process does not send a message on its turn. When this is the case, 
The consensusUpdate protocol should have the following properties:
1. The protocol eventually terminates in all correct processes.
2. If all processes are correct, then the protocol terminates successfully
3. If at least one process is incorrect, then the protocol never terminates successfully in any correct process


 ***************************************************************************)
variables
  state = [
    turnNumber |-> StartingTurnNumber,
    ourIndex |-> self,
    type |-> Types.WAITING
  ],
  me = Participants[self],
  msg = NULL

begin
  (*************************************************************************)
  (*    Each participant either                                            *)
  (*   A. sends a message if it's currently safe to do so, or else         *)
  (*   B. it                                                               *)
  (*     i)   reads a message for the participant                          *)
  (*     ii)  updates their state accordingly and sends a message if it's  *)
  (*          then safe                                                    *)
  (*     iii) removes the message from their inbox.                        *)
  (*                                                                       *)
  (* In the case B, these three actions are currently assumed to be        *)
  (* atomic.                                                               *)
  (*************************************************************************)
  ReachConsensus:
    while Running(state) do
        (*******************************************************************)
        (* When someone is blocking, they don't respond to a force move.   *)
        (* In this case, the channel terminates.  It doesn't matter who    *)
        (* triggers the force move, or whose turn it is.                   *)
        (*******************************************************************)
        if Behaviours[self] = AllowedBehaviours.SLEEP then skip;
        else
            either
                    if ~currentlyOurTurn(state)
                    then
\*                        print("FORCE MOVE");
                        ForceMove:  forceMove(state.turnNumber);
                        WaitForResponse:
                            await challenge.status # ChallengeStatus.ACTIVE;
                            if    challenge.status = ChallengeStatus.RESPONDED then skip;
                            elsif challenge.status = ChallengeStatus.EXPIRED   then terminate(challenge.turnNumber);
                            end if;
                    end if;
            or
                if challenge # NULL
                then
                    ProcessChallenge: processChallenge();
                    RespondToChallenge: respondToChallenge();
                else
                    if currentlyOurTurn(state) then takeAction(state.turnNumber, NumParticipants - 1, me);
                    else 
                        WaitForMessage: with m \in msgs[me] do msg := m end with;
                        ProcessMessage:
                            if msg.status = Status.OK then
                                if msg.turnNumber > state.turnNumber then
                                    if becomesOurTurn(state, msg) then takeAction(msg.turnNumber, msg.votesRequired - 1, me);
                                    else waitForUpdate(msg, me);
                                    end if;
                                else print("Message ignored");
                                end if;
                            elsif msg.status = Status.ABORT   then abort(state.turnNumber, me)
                            elsif msg.status = Status.SUCCESS then returnSuccess(msg.turnNumber, me)
                            end if;
                        RemoveMessage:
                            assert msg # NULL;
                            msgs[me] := msgs[me] \ {msg};
                            msg := NULL;
                        end if;
                end if;
     
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

someoneIsBlocking(idx) == \E p \in idx..NumParticipants : Behaviours[p] = AllowedBehaviours.SLEEP

target(turnNumber) == Participants[mover(turnNumber)]

VARIABLES state, me, msg

vars == << msgs, challenge, pc, state, me, msg >>

ProcSet == (ParticipantIndices)

Init == (* Global variables *)
        /\ msgs = [p \in Names |-> {}]
        /\ challenge = NULL
        (* Process consensusUpdate *)
        /\ state = [self \in ParticipantIndices |->         [
                                                      turnNumber |-> StartingTurnNumber,
                                                      ourIndex |-> self,
                                                      type |-> Types.WAITING
                                                    ]]
        /\ me = [self \in ParticipantIndices |-> Participants[self]]
        /\ msg = [self \in ParticipantIndices |-> NULL]
        /\ pc = [self \in ProcSet |-> "ReachConsensus"]

ReachConsensus(self) == /\ pc[self] = "ReachConsensus"
                        /\ IF Running(state[self])
                              THEN /\ IF Behaviours[self] = AllowedBehaviours.SLEEP
                                         THEN /\ TRUE
                                              /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                              /\ UNCHANGED << msgs, state >>
                                         ELSE /\ \/ /\ IF ~currentlyOurTurn(state[self])
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "ForceMove"]
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                                    /\ UNCHANGED <<msgs, state>>
                                                 \/ /\ IF challenge # NULL
                                                          THEN /\ pc' = [pc EXCEPT ![self] = "ProcessChallenge"]
                                                               /\ UNCHANGED << msgs, 
                                                                               state >>
                                                          ELSE /\ IF currentlyOurTurn(state[self])
                                                                     THEN /\ IF state[self].type = Types.WAITING
                                                                                THEN /\ IF Behaviours[self] = AllowedBehaviours.VOTE
                                                                                           THEN /\ IF (NumParticipants - 1) = 0
                                                                                                      THEN /\ state' = [state EXCEPT ![self] = [ type  |-> Types.SUCCESS,  turnNumber |-> ((state[self].turnNumber)+1)] @@ state[self]]
                                                                                                           /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS, turnNumber |-> ((state'[self].turnNumber)+1)])}]
                                                                                                      ELSE /\ Assert((NumParticipants - 1) > 0, 
                                                                                                                     "Failure of assertion at line 72, column 1 of macro called at line 222, column 53.")
                                                                                                           /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                                   type |-> Types.SENT,
                                                                                                                                                   turnNumber |-> ((state[self].turnNumber)+1),
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
                                                                                                                                "Failure of assertion at line 127, column 14 of macro called at line 222, column 53.")
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
                                                                                                          "Failure of assertion at line 130, column 10 of macro called at line 222, column 53.")
                                                                                                /\ UNCHANGED << msgs, 
                                                                                                                state >>
                                                                          /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForMessage"]
                                                                          /\ UNCHANGED << msgs, 
                                                                                          state >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << msgs, state >>
                        /\ UNCHANGED << challenge, me, msg >>

ForceMove(self) == /\ pc[self] = "ForceMove"
                   /\ Assert(challenge = NULL, 
                             "Failure of assertion at line 144, column 1 of macro called at line 209, column 37.")
                   /\ challenge' =              [
                                     turnNumber |-> (state[self].turnNumber),
                                     status     |-> ChallengeStatus.ACTIVE
                                   ]
                   /\ pc' = [pc EXCEPT ![self] = "WaitForResponse"]
                   /\ UNCHANGED << msgs, state, me, msg >>

WaitForResponse(self) == /\ pc[self] = "WaitForResponse"
                         /\ challenge.status # ChallengeStatus.ACTIVE
                         /\ IF challenge.status = ChallengeStatus.RESPONDED
                               THEN /\ TRUE
                                    /\ state' = state
                               ELSE /\ IF challenge.status = ChallengeStatus.EXPIRED
                                          THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                       type |-> Types.TERMINATED,
                                                                                       turnNumber |-> (challenge.turnNumber)
                                                                                   ] @@ state[self]]
                                          ELSE /\ TRUE
                                               /\ state' = state
                         /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                         /\ UNCHANGED << msgs, challenge, me, msg >>

ProcessChallenge(self) == /\ pc[self] = "ProcessChallenge"
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "RespondToChallenge"]
                          /\ UNCHANGED << msgs, challenge, state, me, msg >>

RespondToChallenge(self) == /\ pc[self] = "RespondToChallenge"
                            /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                            /\ UNCHANGED << msgs, challenge, state, me, msg >>

WaitForMessage(self) == /\ pc[self] = "WaitForMessage"
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
                                                                                                    "Failure of assertion at line 72, column 1 of macro called at line 228, column 72.")
                                                                                          /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                  type |-> Types.SENT,
                                                                                                                                  turnNumber |-> ((msg[self].turnNumber)+1),
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
                                                                                                               "Failure of assertion at line 127, column 14 of macro called at line 228, column 72.")
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
                                                                                         "Failure of assertion at line 130, column 10 of macro called at line 228, column 72.")
                                                                               /\ UNCHANGED << msgs, 
                                                                                               state >>
                                                    ELSE /\ state' = [state EXCEPT ![self] =          [
                                                                                                 turnNumber |-> msg[self].turnNumber,
                                                                                                 type       |-> Types.WAITING,
                                                                                                 ourIndex   |-> state[self].ourIndex
                                                                                             ]]
                                                         /\ msgs' = [msgs EXCEPT ![me[self]] = msgs[me[self]] \ {msg[self]}]
                                         ELSE /\ PrintT(("Message ignored"))
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
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED << msgs, 
                                                                         state >>
                        /\ pc' = [pc EXCEPT ![self] = "RemoveMessage"]
                        /\ UNCHANGED << challenge, me, msg >>

RemoveMessage(self) == /\ pc[self] = "RemoveMessage"
                       /\ Assert(msg[self] # NULL, 
                                 "Failure of assertion at line 237, column 29.")
                       /\ msgs' = [msgs EXCEPT ![me[self]] = msgs[me[self]] \ {msg[self]}]
                       /\ msg' = [msg EXCEPT ![self] = NULL]
                       /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                       /\ UNCHANGED << challenge, state, me >>

consensusUpdate(self) == ReachConsensus(self) \/ ForceMove(self)
                            \/ WaitForResponse(self)
                            \/ ProcessChallenge(self)
                            \/ RespondToChallenge(self)
                            \/ WaitForMessage(self) \/ ProcessMessage(self)
                            \/ RemoveMessage(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ParticipantIndices: consensusUpdate(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ParticipantIndices : WF_vars(consensusUpdate(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllowedMessages ==
  [
    turnNumber: Nat,
    votesRequired : 0..(NumParticipants - 1),
    status: { Status.OK }
  ]
  \cup [
    status: { Status.ABORT, Status.SUCCESS },
    turnNumber: Nat
  ]

States == {} 
  \cup [turnNumber: Nat, ourIndex: ParticipantIndices, type: Range(Types)]

\* Safety properties

TypeOK ==
  \* The following two conditions specify the format of each message and
  \* participant state.
  /\ state \in [ParticipantIndices -> States]
  /\ \A p \in Names : \A m \in msgs[p] : m \in AllowedMessages
  /\ \/ challenge = NULL
     \/ challenge \in [turnNumber: Nat, status: Range(ChallengeStatus)]

\* TODO: Get TurnNumberDoesNotDecrease and StaysTerminated
\* For some reason, state[p].turnNumber' is not valid
TurnNumberDoesNotDecrease ==
  /\ \A p \in ParticipantIndices: state[p].turnNumber' >= state[p].turnNumber

\* Once a process has terminated, its state does not change.
StaysTerminated == \A p \in ParticipantIndices: (Terminated(state[p]) => (state'[p] = state[p]))
  
\* Liveness properties
ProtocolTerminates == 
    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.SUCCESS
                                          /\ state[p].turnNumber = StartingTurnNumber + NumParticipants))
    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.FAILURE
                                          /\ state[p].turnNumber = state[1].turnNumber))
    
\* The value of msg should eventually always be NULL
MessagesAreRead == <>[](msgs = [p \in ParticipantIndices |-> {"Foo"}])

=============================================================================
\* Modification History
\* Last modified Tue Aug 20 11:17:36 PDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
