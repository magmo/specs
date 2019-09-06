----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Alice,
    Eve,
    StartingTurnNumber,
    NumParticipants,
    AlicesIDX,
    NULL \* A model value representing null.

ChannelMode == [
  OPEN |-> "OPEN",
  CHALLENGE  |-> "CHALLENGE",
  FINALIZED |-> "FINALIZED"
]


TX_Type == [
  CHALLENGE |-> "CHALLENGE"
]

Range(f) == { f[x] : x \in DOMAIN f }

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
AlicesGoalTurnNumber == LatestTurnNumber + 1
Names == { Alice, Eve }
ParticipantIDXs == 1..NumParticipants
AlicesCommitments == StartingTurnNumber..LatestTurnNumber

ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX
Actor(commitment) == IF commitment.signer = AlicesIDX THEN Alice ELSE Eve

Maximum(a,b) == IF a > b THEN a ELSE b

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
  /\ AlicesIDX \in ParticipantIDXs
  /\ ~AlicesMove(LatestTurnNumber + 1)
            
(* --algorithm forceMove

variables
    channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ],
    tx_pool = <<>>

define
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)
    
AliceCanTakeAction == channel.mode # ChannelMode.FINALIZED
EveCanTakeAction == AliceCanTakeAction

Refutable(n) == TRUE
    /\ n % NumParticipants = channel.challenge.signer % NumParticipants
    /\ n > channel.challenge.turnNumber
end define;

macro clearChallenge(turnNumber)
begin
assert turnNumber \in Nat;
channel := [
    mode |-> ChannelMode.OPEN,
    turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], turnNumber)],
    challenge |-> NULL
];
end macro;


macro submitChallenge(commitment, actor)
begin
assert actor \notin DOMAIN tx_pool;
tx_pool := [p \in { actor } |-> [ type |-> TX_Type.CHALLENGE ] @@ commitment ] @@ tx_pool;
end macro;

macro respondWithMove(commitment)
begin
if
    /\ challengeOngoing
    /\ validTransition(commitment)
then clearChallenge(commitment.turnNumber);
else
    assert FALSE;
end if;
end macro;

macro respondWithAlternativeMove(commitment)
begin
if
    /\ challengeOngoing
    /\ commitment.turnNumber > channel.challenge.turnNumber + 1
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro refute(turnNumber)
begin
if
    /\ challengeOngoing
    /\ turnNumber > channel.turnNumber[ParticipantIDX(turnNumber)]
then
channel := [
    mode |-> ChannelMode.OPEN,
    challenge  |-> NULL,
    turnNumber |-> [i \in {ParticipantIDX(turnNumber)} |-> turnNumber] @@ channel.turnNumber  
];
end if;
end macro;

macro forceMove(commitment)
begin
assert validCommitment(commitment);
if
    /\ channelOpen
    /\ progressesChannel(commitment)
then submitChallenge(commitment, Actor(commitment))
end if;

end macro;

fair process adjudicator = "Adjudicator"
begin
(***************************************************************************)
(* This process records submitted channels.                                *)
(***************************************************************************)
Adjudicator:
while
    \/ AliceCanTakeAction
    \/ EveCanTakeAction
do
    if \E x \in DOMAIN tx_pool: TRUE then
        with actor \in DOMAIN tx_pool,
             tx = tx_pool[actor]
        do
            channel := [ mode |-> ChannelMode.CHALLENGE, challenge |-> [turnNumber |-> tx.turnNumber, signer |-> tx.signer] ] @@ channel;
            tx_pool := [p \in (DOMAIN tx_pool) \ {actor} |-> tx_pool[actor]];
        end with;
    end if;
end while;
end process;

fair process alice = Alice
begin
(***************************************************************************)
(* Alice has commitments (n - numParticipants)..(n-1).  She wants to end   *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* She is allowed to:                                                      *)
(*   - Call forceMove with any states that she currently has               *)
(*   - Call refute with any state that she has                             *)
(*   - Call respondWithMove or respondWithMove whenever there's an active  *)
(*     challenge where it's her turn to move                               *)
(***************************************************************************)
AliceMoves:
while AliceCanTakeAction
do
    if challengeOngoing then
        if
            /\ channel.challenge.turnNumber < StartingTurnNumber
        then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She can therefore call refute with exactly one commitment, according to
            \* the channel's current turnNumber.
            Refute:
                refute(
                    CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer
                );
        elsif
            /\ channel.challenge.turnNumber >= StartingTurnNumber
            /\ AlicesMove(channel.challenge.turnNumber+1)
        then
            Respond:
                respondWithMove([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]);
        else
            \* Alice has run out of allowed actions, resulting in the channel being finalized
            Finalize:
                channel := [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel;
        end if;
    elsif Alice \notin DOMAIN tx_pool then
        forceMove([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]);
    end if;
end while;
end process;

fair process eve = Eve
begin
(***************************************************************************)
(* Eve can do almost anything.                                             *)
(*                                                                         *)
(*   - She can sign any data with any private key, except she cannot sign  *)
(*     a commitment with Alice's private key when the turn number is       *)
(*     greater than or equal to StartingTurnNumber                         *)
(*   - She can call any adjudicator function, at any time                  *)
(*   - She can front-run any transaction an arbitrary number of times: if  *)
(*     anyone else calls an adjudicator function in a transaction tx, she  *)
(*     can then choose to submit any transaction before tx is mined.       *)
(*   - She can choose not to do anything, thus causing any active          *)
(*     challenge to expire.                                                *)
(***************************************************************************)
EveMoves:
while EveCanTakeAction do
    await Eve \notin DOMAIN tx_pool;
    either ForceMove:
        with n \in NumParticipants..LatestTurnNumber,
             idx \in ParticipantIDXs \ { AlicesIDX }
        do
            forceMove([ turnNumber |-> n, signer |-> idx ]);
        end with;
    or Respond:
        if
            /\ challengeOngoing
            /\ ~AlicesMove(channel.challenge.turnNumber)
        then skip;
\*            respondWithMove([
\*                turnNumber |-> channel.challenge.turnNumber + 1,
\*                signer |-> ParticipantIDX(channel.challenge.turnNumber)
\*            ]);
        end if;
    or Refute:
        if
            /\ challengeOngoing
            /\ ~AlicesMove(channel.challenge.turnNumber)
        then skip;
        end if;
    end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
\* Label Refute of process alice at line 104 col 1 changed to Refute_
\* Label Respond of process alice at line 84 col 1 changed to Respond_
VARIABLES channel, tx_pool, pc

(* define statement *)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)

AliceCanTakeAction == channel.mode # ChannelMode.FINALIZED
EveCanTakeAction == AliceCanTakeAction

Refutable(n) == TRUE
    /\ n % NumParticipants = channel.challenge.signer % NumParticipants
    /\ n > channel.challenge.turnNumber


vars == << channel, tx_pool, pc >>

ProcSet == {"Adjudicator"} \cup {Alice} \cup {Eve}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ]
        /\ tx_pool = <<>>
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = Alice -> "AliceMoves"
                                        [] self = Eve -> "EveMoves"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF \/ AliceCanTakeAction
                     \/ EveCanTakeAction
                     THEN /\ IF \E x \in DOMAIN tx_pool: TRUE
                                THEN /\ \E actor \in DOMAIN tx_pool:
                                          LET tx == tx_pool[actor] IN
                                            /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> [turnNumber |-> tx.turnNumber, signer |-> tx.signer] ] @@ channel
                                            /\ tx_pool' = [p \in (DOMAIN tx_pool) \ {actor} |-> tx_pool[actor]]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << channel, tx_pool >>
                          /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                          /\ UNCHANGED << channel, tx_pool >>

adjudicator == Adjudicator

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF AliceCanTakeAction
                    THEN /\ IF challengeOngoing
                               THEN /\ IF /\ channel.challenge.turnNumber < StartingTurnNumber
                                          THEN /\ pc' = [pc EXCEPT ![Alice] = "Refute_"]
                                          ELSE /\ IF /\ channel.challenge.turnNumber >= StartingTurnNumber
                                                     /\ AlicesMove(channel.challenge.turnNumber+1)
                                                     THEN /\ pc' = [pc EXCEPT ![Alice] = "Respond_"]
                                                     ELSE /\ pc' = [pc EXCEPT ![Alice] = "Finalize"]
                                    /\ UNCHANGED tx_pool
                               ELSE /\ IF Alice \notin DOMAIN tx_pool
                                          THEN /\ Assert(validCommitment(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ])), 
                                                         "Failure of assertion at line 118, column 1 of macro called at line 186, column 9.")
                                               /\ IF /\ channelOpen
                                                     /\ progressesChannel(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]))
                                                     THEN /\ Assert((Actor(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]))) \notin DOMAIN tx_pool, 
                                                                    "Failure of assertion at line 78, column 1 of macro called at line 186, column 9.")
                                                          /\ tx_pool' = [p \in { (Actor(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]))) } |-> [ type |-> TX_Type.CHALLENGE ] @@ ([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]) ] @@ tx_pool
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED tx_pool
                                          ELSE /\ TRUE
                                               /\ UNCHANGED tx_pool
                                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
                         /\ UNCHANGED tx_pool
              /\ UNCHANGED channel

Refute_ == /\ pc[Alice] = "Refute_"
           /\ IF /\ challengeOngoing
                 /\ (CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer) > channel.turnNumber[ParticipantIDX((CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer))]
                 THEN /\ channel' =            [
                                        mode |-> ChannelMode.OPEN,
                                        challenge  |-> NULL,
                                        turnNumber |-> [i \in {ParticipantIDX((CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer))} |-> (CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer)] @@ channel.turnNumber
                                    ]
                 ELSE /\ TRUE
                      /\ UNCHANGED channel
           /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
           /\ UNCHANGED tx_pool

Respond_ == /\ pc[Alice] = "Respond_"
            /\ IF /\ challengeOngoing
                  /\ validTransition(([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]))
                  THEN /\ Assert((([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]).turnNumber) \in Nat, 
                                 "Failure of assertion at line 67, column 1 of macro called at line 179, column 17.")
                       /\ channel' =            [
                                         mode |-> ChannelMode.OPEN,
                                         turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], (([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]).turnNumber))],
                                         challenge |-> NULL
                                     ]
                  ELSE /\ Assert(FALSE, 
                                 "Failure of assertion at line 89, column 5 of macro called at line 179, column 17.")
                       /\ UNCHANGED channel
            /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
            /\ UNCHANGED tx_pool

Finalize == /\ pc[Alice] = "Finalize"
            /\ channel' = [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel
            /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
            /\ UNCHANGED tx_pool

alice == AliceMoves \/ Refute_ \/ Respond_ \/ Finalize

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ IF EveCanTakeAction
                  THEN /\ Eve \notin DOMAIN tx_pool
                       /\ \/ /\ pc' = [pc EXCEPT ![Eve] = "ForceMove"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "Respond"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "Refute"]
                  ELSE /\ pc' = [pc EXCEPT ![Eve] = "Done"]
            /\ UNCHANGED << channel, tx_pool >>

ForceMove == /\ pc[Eve] = "ForceMove"
             /\ \E n \in NumParticipants..LatestTurnNumber:
                  \E idx \in ParticipantIDXs \ { AlicesIDX }:
                    /\ Assert(validCommitment(([ turnNumber |-> n, signer |-> idx ])), 
                              "Failure of assertion at line 118, column 1 of macro called at line 213, column 13.")
                    /\ IF /\ channelOpen
                          /\ progressesChannel(([ turnNumber |-> n, signer |-> idx ]))
                          THEN /\ Assert((Actor(([ turnNumber |-> n, signer |-> idx ]))) \notin DOMAIN tx_pool, 
                                         "Failure of assertion at line 78, column 1 of macro called at line 213, column 13.")
                               /\ tx_pool' = [p \in { (Actor(([ turnNumber |-> n, signer |-> idx ]))) } |-> [ type |-> TX_Type.CHALLENGE ] @@ ([ turnNumber |-> n, signer |-> idx ]) ] @@ tx_pool
                          ELSE /\ TRUE
                               /\ UNCHANGED tx_pool
             /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
             /\ UNCHANGED channel

Respond == /\ pc[Eve] = "Respond"
           /\ IF /\ challengeOngoing
                 /\ ~AlicesMove(channel.challenge.turnNumber)
                 THEN /\ TRUE
                 ELSE /\ TRUE
           /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
           /\ UNCHANGED << channel, tx_pool >>

Refute == /\ pc[Eve] = "Refute"
          /\ IF /\ challengeOngoing
                /\ ~AlicesMove(channel.challenge.turnNumber)
                THEN /\ TRUE
                ELSE /\ TRUE
          /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
          /\ UNCHANGED << channel, tx_pool >>

eve == EveMoves \/ ForceMove \/ Respond \/ Refute

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == adjudicator \/ alice \/ eve
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ WF_vars(alice)
        /\ WF_vars(eve)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
AllowedChallenges == [ turnNumber: AllowedTurnNumbers, signer: ParticipantIDXs ]

AllowedTransactions == { c @@ [  type |-> TX_Type.CHALLENGE ] : c \in AllowedChallenges }
AllowedChannels == [ turnNumber: [ParticipantIDXs -> Nat] , mode: Range(ChannelMode), challenge: AllowedChallenges \cup { NULL } ]

\* Safety properties

TypeOK ==
  /\ channel \in AllowedChannels
  /\ tx_pool \in UNION { [ S -> AllowedTransactions ] : S \in SUBSET { Alice, Eve } }
  
\* Liveness properties
AliceCanProgressChannel == <>[](
    /\ channel.mode = ChannelMode.OPEN
    /\ channel.turnNumber[AlicesIDX] = AlicesGoalTurnNumber
)

FinalizedWithLatestTurnNumber == <>[](
    /\ channel.mode = ChannelMode.FINALIZED
    /\ channel.turnNumber[AlicesIDX] = LatestTurnNumber
)

AliceDoesNotLoseFunds ==
    \/ AliceCanProgressChannel
    \/ FinalizedWithLatestTurnNumber


\* These properties and invariants let us ensure that the model does actually find behaviours where
\* Eve can "front-run".
\* The first lets us ensure that Eve can place a transaction in the pool even when Alice has one in the pool.
\* The second lets us ensures that if both Alice and Eve have transactions in the pool, then it's possible that Eve's is processed first.

EveNeverFrontRuns == DOMAIN tx_pool # { Alice, Eve }
AdjudicatorNeverProcessesEveFirst == [][
    IF   DOMAIN tx_pool = { Alice, Eve }
    THEN Eve \in DOMAIN tx_pool'
    ELSE TRUE
]_<<tx_pool>>

=============================================================================
\* Modification History
\* Last modified Fri Sep 06 15:42:37 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
