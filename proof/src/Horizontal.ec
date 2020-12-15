require import AllCore List SmtMap Distr IntDiv DMap FSet.

require import ALanguage ASecretSharingScheme AProtocolLibrary AAPI ASPSemantics AMPSemantics.
require import MPCProtocolLibrary ProtocolAPI SPAPISemantics MPAPISemantics.
require import MPProtocolAPISemantics.
require import Utils.

import SS.
import MPCLib.
import MPCAPI.

theory Compilation.

clone import Language as L.

clone import MultiPartyProtocolAPISemantics as Source with
 type L1.L = L,
 type L2.L = L,
 type L3.L = L,
  type MultiPartyAPISemantics.SemP2.EnvL = MultiPartyAPISemantics.SemP1.EnvL,
  type MultiPartyAPISemantics.SemP3.EnvL = MultiPartyAPISemantics.SemP1.EnvL,
  op MultiPartyAPISemantics.SemP2.stepL = MultiPartyAPISemantics.SemP1.stepL,
  op MultiPartyAPISemantics.SemP3.stepL = MultiPartyAPISemantics.SemP1.stepL,
  op MultiPartyAPISemantics.SemP2.stepPiter = MultiPartyAPISemantics.SemP1.stepPiter,
  op MultiPartyAPISemantics.SemP3.stepPiter = MultiPartyAPISemantics.SemP2.stepPiter.

(* The REAL API *)
module API_Real : API.API_t = {
var senv: (svar_t, sharedValue_t) fmap
proc init(): unit = {
  senv <- empty;
}
proc nparties(): int = { return SecretSharingScheme.n; }
proc declass(a: svar_t): (value_t * sideInfo_t) option = {
  var vtr, r;
   r <- None;
   if (a \in senv) {
    vtr <@ APIsec.prot_declass(oget senv.[a]);
     r <- Some vtr;
   }
  return r;
}
proc input(a : svar_t, inp: sharedValue_t): sideInfo_t option = {
  var tr;
   tr <@ APIsec.prot_in(inp);
  senv <- senv.[ a <- inp ];
  return Some tr;
}
proc output(a: svar_t): (sharedValue_t * sideInfo_t) option = {
  var o, tr, r;
   r <- None;
   if (a \in senv) {
     (o, tr) <@ APIsec.prot_out(oget (senv.[a]));
     r <- Some (o, tr);
   }
  return r;
}
proc sop(sop: MPCLib.sop_t, pargs: value_t list, sargs: svar_t list, a : svar_t) : sideInfo_t option = {
  var r, tr, y;
   r <- None;
   if (forall x, x \in sargs /\ x \in senv) {
     (y, tr) <@ APIsec.prot_sop(sop,pargs, map (fun x => oget senv.[x]) sargs);
     senv <- senv.[ a <- y ];
     r <- Some tr;
   }
  return r;
}
}.

import MultiPartyAPISemantics.
import MultiPartySemantics.

lemma nosmt stepP_spec_h i st':
   hoare [ ProgSem(API_Real).stepP :
           id = i /\ ProgSem.st = st'
          ==>
           ProgSem.st = (if i = P1 then 
                          {| st' with StP1 = oget (SemP1.stepPiter SemP1.stepL (b2i res) (st'.`StP1)) |}
                        else if i = P2 then
                          {| st' with StP2 = oget (SemP2.stepPiter SemP2.stepL (b2i res) (st'.`StP2)) |}
                        else 
                          {| st' with StP3 = oget (SemP3.stepPiter SemP3.stepL (b2i res) (st'.`StP3)) |}) /\
           res = if i = P1 then (SemP1.stepPiter SemP1.stepL 1 (st'.`StP1) <> None)
                 else if i = P2 then (SemP2.stepPiter SemP2.stepL 1 (st'.`StP2) <> None)
                 else (SemP3.stepPiter SemP3.stepL 1 (st'.`StP3) <> None)
         ].
proof.
proc. 
case (i = P1).
wp; skip; progress.
rewrite /upd_Sigma1 => //=.
congr.
rewrite /b2i => /=.
rewrite SemP1.stepPiter1.
done.
smt().
rewrite SemP1.stepPiter1.
done.
smt().
rewrite /b2i => /=. 
rewrite SemP1.stepPiter0 => /=.
done.
smt().
rewrite SemP1.stepPiter1.
done.
smt().
rewrite /b2i => /=. 
rewrite SemP1.stepPiter0 => /=.
done.
smt().
smt(SemP1.callSt_stepPiter).
case (i = P2).
wp; skip; progress.
rewrite /upd_Sigma2 => //=.
congr.
rewrite /b2i => /=.
rewrite SemP2.stepPiter1.
done.
smt().
rewrite SemP2.stepPiter1.
done.
smt().
rewrite /b2i => /=. 
rewrite SemP2.stepPiter0 => /=.
done.
smt().
rewrite SemP2.stepPiter1.
done.
smt().
rewrite /b2i => /=. 
rewrite SemP2.stepPiter0 => /=.
done.
smt().
smt(SemP2.callSt_stepPiter).
case (i = P3).
wp; skip; progress.
rewrite /upd_Sigma3 => //=.
congr.
rewrite /b2i => /=.
rewrite SemP3.stepPiter1.
done.
smt().
rewrite SemP3.stepPiter1.
done.
smt().
rewrite /b2i => /=. 
rewrite SemP3.stepPiter0 => /=.
done.
smt().
rewrite SemP3.stepPiter1.
done.
smt().
rewrite /b2i => /=. 
rewrite SemP3.stepPiter0 => /=.
done.
smt().
smt(SemP3.callSt_stepPiter).
exfalso => /#.
qed.

lemma nosmt stepP_ll: islossless ProgSem(API_Real).stepP.
proof. by proc; wp; skip; progress => /#. qed.

lemma nosmt stepP_spec i st': 
  phoare [ ProgSem(API_Real).stepP :
           id = i /\ ProgSem.st = st'
          ==>
           ProgSem.st = (if i = P1 then 
                          {| st' with StP1 = oget (SemP1.stepPiter SemP1.stepL (b2i res) (st'.`StP1)) |}
                        else if i = P2 then
                          {| st' with StP2 = oget (SemP2.stepPiter SemP2.stepL (b2i res) (st'.`StP2)) |}
                        else 
                          {| st' with StP3 = oget (SemP3.stepPiter SemP3.stepL (b2i res) (st'.`StP3)) |}) /\
           res = if i = P1 then (SemP1.stepPiter SemP1.stepL 1 (st'.`StP1) <> None)
                 else if i = P2 then (SemP2.stepPiter SemP2.stepL 1 (st'.`StP2) <> None)
                 else (SemP3.stepPiter SemP3.stepL 1 (st'.`StP3) <> None)
         ] = 1%r.
proof. by conseq stepP_ll (stepP_spec_h i st'). qed.

clone import Language as L1'.
clone import Language as L2'.
clone import Language as L3'.

clone import MultiPartyProtocolAPISemantics as Target with
  type L1.L = L1'.L,
  type L2.L = L2'.L,
  type L3.L = L3'.L
rename "MultiPartyAPISemantics.GlobalSt" as "TGlobalSt".
(*import MultiPartyAPISemantics.
import MultiPartySemantics.*)

(** COMPILERS **)

(* Compiler Correctness *)

(* equivalence relation on source/target local states *)
op equivLSt ['ls, 'es, 'lt, 'et] : ('ls*'es) -> ('lt*'et) -> bool.

op equivSt1 ['ls, 'es, 'lt, 'et] (s:('ls,'es) Source.MultiPartyAPISemantics.SemP1.APIst) (s':('lt,'et) Target.MultiPartyAPISemantics.SemP1.APIst) =
 s.`1 = s'.`1 /\ equivLSt s.`2 s'.`2.
op equivSt2 ['ls, 'es, 'lt, 'et] (s:('ls,'es) Source.MultiPartyAPISemantics.SemP2.APIst) (s':('lt,'et) Target.MultiPartyAPISemantics.SemP2.APIst) =
 s.`1 = s'.`1 /\ equivLSt s.`2 s'.`2.
op equivSt3 ['ls, 'es, 'lt, 'et] (s:('ls,'es) Source.MultiPartyAPISemantics.SemP3.APIst) (s':('lt,'et) Target.MultiPartyAPISemantics.SemP3.APIst) =
 s.`1 = s'.`1 /\ equivLSt s.`2 s'.`2.

lemma equivSt_callSt1 ['ls, 'es, 'lt, 'et]
 (s1: ('ls, 'es) Source.MultiPartyAPISemantics.SemP1.APIst) (s2: ('lt, 'et) Target.MultiPartyAPISemantics.SemP1.APIst):
 equivSt1 s1 s2 => SemP1.callSt s1 = SemP1.callSt s2.
proof.
by rewrite /equivSt /callSt; move => [-> _].
qed.
lemma equivSt_callSt2 ['ls, 'es, 'lt, 'et]
 (s1: ('ls, 'es) Source.MultiPartyAPISemantics.SemP2.APIst) (s2: ('lt, 'et) Target.MultiPartyAPISemantics.SemP2.APIst):
 equivSt2 s1 s2 => SemP2.callSt s1 = SemP2.callSt s2.
proof.
by rewrite /equivSt /callSt; move => [-> _].
qed.
lemma equivSt_callSt3 ['ls, 'es, 'lt, 'et]
 (s1: ('ls, 'es) Source.MultiPartyAPISemantics.SemP3.APIst) (s2: ('lt, 'et) Target.MultiPartyAPISemantics.SemP3.APIst):
 equivSt3 s1 s2 => SemP3.callSt s1 = SemP3.callSt s2.
proof.
by rewrite /equivSt /callSt; move => [-> _].
qed.

(* compilers *)
op compiler1 : L.L -> L1.L.
op compiler2 : L.L -> L2.L.
op compiler3 : L.L -> L3.L.

(* ASSUMPTION: equivalence of initial states *)
axiom equivSt_init1 (P:L.L):
  equivSt1 (Source.MultiPartyAPISemantics.SemP1.initSt (Source.MultiPartyAPISemantics.SemP1.initStateL P)) (Target.MultiPartyAPISemantics.SemP1.initSt (Target.MultiPartyAPISemantics.SemP1.initStateL (compiler1 P))).
axiom equivSt_init2 (P:L.L):
  equivSt2 (Source.MultiPartyAPISemantics.SemP2.initSt (Source.MultiPartyAPISemantics.SemP2.initStateL P)) (Target.MultiPartyAPISemantics.SemP2.initSt (Target.MultiPartyAPISemantics.SemP2.initStateL (compiler2 P))).
axiom equivSt_init3 (P:L.L):
  equivSt3 (Source.MultiPartyAPISemantics.SemP3.initSt (Source.MultiPartyAPISemantics.SemP3.initStateL P)) (Target.MultiPartyAPISemantics.SemP3.initSt (Target.MultiPartyAPISemantics.SemP3.initStateL (compiler3 P))).

(* ASSUMPTION: backward simulation (trace preservation) *)
axiom bisim_backward1 ss st kt st':
 equivSt1 ss st =>
 Target.MultiPartyAPISemantics.SemP1.stepPiter Target.MultiPartyAPISemantics.SemP1.stepL kt st = Some st' =>
 Target.MultiPartyAPISemantics.SemP1.callSt st' <> None =>
 (exists ks ss', Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL ks ss = Some ss'
                 /\ equivSt1 ss' st' /\ 0 <= ks).

axiom bisim_backward2 ss st kt st':
 equivSt2 ss st =>
 Target.MultiPartyAPISemantics.SemP2.stepPiter Target.MultiPartyAPISemantics.SemP2.stepL kt st = Some st' =>
 Target.MultiPartyAPISemantics.SemP2.callSt st' <> None =>
 (exists ks ss', Source.MultiPartyAPISemantics.SemP2.stepPiter Source.MultiPartyAPISemantics.SemP2.stepL ks ss = Some ss'
                 /\ equivSt2 ss' st' /\ 0 <= ks).

axiom bisim_backward3 ss st kt st':
 equivSt3 ss st =>
 Target.MultiPartyAPISemantics.SemP3.stepPiter Target.MultiPartyAPISemantics.SemP3.stepL kt st = Some st' =>
 Target.MultiPartyAPISemantics.SemP3.callSt st' <> None =>
 (exists ks ss', Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL ks ss = Some ss'
                 /\ equivSt3 ss' st' /\ 0 <= ks).

(* handling different paces among parties *)
print Target.MultiPartyAPISemantics.SemP1.stepL.

op advSt1
(step : L1.L -> Target.MultiPartyAPISemantics.SemP1.EnvL -> Target.MultiPartyAPISemantics.SemP1.API.apiRes_data option -> (L1.L, Target.MultiPartyAPISemantics.SemP1.EnvL) Target.MultiPartyAPISemantics.SemP1.ECall option)
(ss: (L.L, Source.MultiPartyAPISemantics.SemP1.EnvL) Source.MultiPartyAPISemantics.SemP1.APIst) 
(st: (L1.L, Target.MultiPartyAPISemantics.SemP1.EnvL) Target.MultiPartyAPISemantics.SemP1.APIst) : bool =
 exists n st', 0 <= n /\ equivSt1 ss st' /\ Target.MultiPartyAPISemantics.SemP1.stepPiter step n st' = Some st.

lemma advS01 (step : L1.L -> Target.MultiPartyAPISemantics.SemP1.EnvL -> Target.MultiPartyAPISemantics.SemP1.API.apiRes_data option -> (L1.L, Target.MultiPartyAPISemantics.SemP1.EnvL) Target.MultiPartyAPISemantics.SemP1.ECall option) 
(s1 :  (L.L, Source.MultiPartyAPISemantics.SemP1.EnvL) Source.MultiPartyAPISemantics.SemP1.APIst)
(s2: (L1.L, Target.MultiPartyAPISemantics.SemP1.EnvL) Target.MultiPartyAPISemantics.SemP1.APIst):
 equivSt1 s1 s2 => advSt1 step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite Target.MultiPartyAPISemantics.SemP1.stepPiter0.
qed.

lemma nosmt advSt_callSt1 (step : L1.L -> Target.MultiPartyAPISemantics.SemP1.EnvL -> Target.MultiPartyAPISemantics.SemP1.API.apiRes_data option -> (L1.L, Target.MultiPartyAPISemantics.SemP1.EnvL) Target.MultiPartyAPISemantics.SemP1.ECall option) 
(s1 :  (L.L, Source.MultiPartyAPISemantics.SemP1.EnvL) Source.MultiPartyAPISemantics.SemP1.APIst)
(s2: (L1.L, Target.MultiPartyAPISemantics.SemP1.EnvL) Target.MultiPartyAPISemantics.SemP1.APIst):
 advSt1 step s1 s2 =>
 Target.MultiPartyAPISemantics.SemP1.callSt s1 <> None =>
 equivSt1 s1 s2.
proof.
move=> [k st'] /> *.
have ?: Target.MultiPartyAPISemantics.SemP1.callSt st' <> None by smt().
move: (Target.MultiPartyAPISemantics.SemP1.callSt_stepPiter step k st' H4); move=> [?|?].
 by move: H2; rewrite Target.MultiPartyAPISemantics.SemP1.stepPiter0 //.
by move: H2; rewrite H5.
qed.

op advSt2
(step : L2.L -> Target.MultiPartyAPISemantics.SemP2.EnvL -> Target.MultiPartyAPISemantics.SemP2.API.apiRes_data option -> (L2.L, Target.MultiPartyAPISemantics.SemP2.EnvL) Target.MultiPartyAPISemantics.SemP2.ECall option)
(ss: (L.L, Source.MultiPartyAPISemantics.SemP2.EnvL) Source.MultiPartyAPISemantics.SemP2.APIst) 
(st: (L2.L, Target.MultiPartyAPISemantics.SemP2.EnvL) Target.MultiPartyAPISemantics.SemP2.APIst) : bool =
 exists n st', 0 <= n /\ equivSt2 ss st' /\ Target.MultiPartyAPISemantics.SemP2.stepPiter step n st' = Some st.

lemma advS02 (step : L2.L -> Target.MultiPartyAPISemantics.SemP2.EnvL -> Target.MultiPartyAPISemantics.SemP2.API.apiRes_data option -> (L2.L, Target.MultiPartyAPISemantics.SemP2.EnvL) Target.MultiPartyAPISemantics.SemP2.ECall option) 
(s1 :  (L.L, Source.MultiPartyAPISemantics.SemP2.EnvL) Source.MultiPartyAPISemantics.SemP2.APIst)
(s2: (L2.L, Target.MultiPartyAPISemantics.SemP2.EnvL) Target.MultiPartyAPISemantics.SemP2.APIst):
 equivSt2 s1 s2 => advSt2 step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite Target.MultiPartyAPISemantics.SemP2.stepPiter0.
qed.

lemma nosmt advSt_callSt2 (step : L2.L -> Target.MultiPartyAPISemantics.SemP2.EnvL -> Target.MultiPartyAPISemantics.SemP2.API.apiRes_data option -> (L2.L, Target.MultiPartyAPISemantics.SemP2.EnvL) Target.MultiPartyAPISemantics.SemP2.ECall option) 
(s1 :  (L.L, Source.MultiPartyAPISemantics.SemP2.EnvL) Source.MultiPartyAPISemantics.SemP2.APIst)
(s2: (L2.L, Target.MultiPartyAPISemantics.SemP2.EnvL) Target.MultiPartyAPISemantics.SemP2.APIst):
 advSt2 step s1 s2 =>
 Target.MultiPartyAPISemantics.SemP2.callSt s1 <> None =>
 equivSt2 s1 s2.
proof.
move=> [k st'] /> *.
have ?: Target.MultiPartyAPISemantics.SemP2.callSt st' <> None by smt().
move: (Target.MultiPartyAPISemantics.SemP2.callSt_stepPiter step k st' H4); move=> [?|?].
 by move: H2; rewrite Target.MultiPartyAPISemantics.SemP2.stepPiter0 //.
by move: H2; rewrite H5.
qed.

op advSt3
(step : L3.L -> Target.MultiPartyAPISemantics.SemP3.EnvL -> Target.MultiPartyAPISemantics.SemP3.API.apiRes_data option -> (L3.L, Target.MultiPartyAPISemantics.SemP3.EnvL) Target.MultiPartyAPISemantics.SemP3.ECall option)
(ss: (L.L, Source.MultiPartyAPISemantics.SemP3.EnvL) Source.MultiPartyAPISemantics.SemP3.APIst) 
(st: (L3.L, Target.MultiPartyAPISemantics.SemP3.EnvL) Target.MultiPartyAPISemantics.SemP3.APIst) : bool =
 exists n st', 0 <= n /\ equivSt3 ss st' /\ Target.MultiPartyAPISemantics.SemP3.stepPiter step n st' = Some st.

lemma advS03 (step : L3.L -> Target.MultiPartyAPISemantics.SemP3.EnvL -> Target.MultiPartyAPISemantics.SemP3.API.apiRes_data option -> (L3.L, Target.MultiPartyAPISemantics.SemP3.EnvL) Target.MultiPartyAPISemantics.SemP3.ECall option) 
(s1 :  (L.L, Source.MultiPartyAPISemantics.SemP3.EnvL) Source.MultiPartyAPISemantics.SemP3.APIst)
(s2: (L3.L, Target.MultiPartyAPISemantics.SemP3.EnvL) Target.MultiPartyAPISemantics.SemP3.APIst):
 equivSt3 s1 s2 => advSt3 step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite Target.MultiPartyAPISemantics.SemP3.stepPiter0.
qed.

lemma nosmt advSt_callSt3 (step : L3.L -> Target.MultiPartyAPISemantics.SemP3.EnvL -> Target.MultiPartyAPISemantics.SemP3.API.apiRes_data option -> (L3.L, Target.MultiPartyAPISemantics.SemP3.EnvL) Target.MultiPartyAPISemantics.SemP3.ECall option) 
(s1 :  (L.L, Source.MultiPartyAPISemantics.SemP3.EnvL) Source.MultiPartyAPISemantics.SemP3.APIst)
(s2: (L3.L, Target.MultiPartyAPISemantics.SemP3.EnvL) Target.MultiPartyAPISemantics.SemP3.APIst):
 advSt3 step s1 s2 =>
 Target.MultiPartyAPISemantics.SemP3.callSt s1 <> None =>
 equivSt3 s1 s2.
proof.
move=> [k st'] /> *.
have ?: Target.MultiPartyAPISemantics.SemP3.callSt st' <> None by smt().
move: (Target.MultiPartyAPISemantics.SemP3.callSt_stepPiter step k st' H4); move=> [?|?].
 by move: H2; rewrite Target.MultiPartyAPISemantics.SemP3.stepPiter0 //.
by move: H2; rewrite H5.
qed.

module RealSemMT = Target.ProgSem(API_Real).
module RealSem = Source.ProgSem(API_Real).

module AdvOrclMT (Sem: AdvSemInterface) : AdvSemInterface = {
  (* Simulator runs a local copy of all parties... *)
  module SemEmu = RealSemMT
  include SemEmu [- init, stepP, stepS]

  proc init(P1:L1.L, P2:L2.L, P3:L3.L): unit = {
    SemEmu.init(P1,P2,P3);
  }
  (* [stepP] relies on the local [RealSemMT] module in order to
     control the execution of each party.
     It leaves [Sem] untouched *)
  proc stepP = SemEmu.stepP
  (* Step Secret *)
  proc stepS(): sideInfo_t option = {
    var b, i, v;
    var r <- None;
    var ecall <- Target.syncPoint (Target.MultiPartyAPISemantics.SemP1.callSt (Target.MultiPartyAPISemantics.StP1 SemEmu.st),
                            Target.MultiPartyAPISemantics.SemP2.callSt (Target.MultiPartyAPISemantics.StP2 SemEmu.st),
                            Target.MultiPartyAPISemantics.SemP3.callSt (Target.MultiPartyAPISemantics.StP3 SemEmu.st));
    if (ecall <> None) { (* call to the API *)
      (* advance the source into a sync-point *)
      i <- 0;
      b <- true;
      while (b) {
        b <@  Sem.stepP(P1);
        b <@  Sem.stepP(P2);
        b <@  Sem.stepP(P3);
        i <- i + 1;
      }
      (* do a [stepS] at the source *)
      r <@ Sem.stepS();
      if (r <> None) {
          match (oget ecall) with
          | Call_declass a => { v <- leakage_value (oget (oget r).`leakage);
                                (* updates API result *)
                                RealSemMT.st <- Target.MultiPartyAPISemantics.upd_SigmaAPI (Some (oget v)) RealSemMT.st;
                              }
          | Call_in a => { RealSemMT.st <- Target.MultiPartyAPISemantics.upd_SigmaAPI None RealSemMT.st; (* resets call *)
                         }
          | Call_out a => { RealSemMT.st <- Target.MultiPartyAPISemantics.upd_SigmaAPI None RealSemMT.st; (* resets call *)
                          }
      | Call_sop o a pargs sargs => { RealSemMT.st <- Target.MultiPartyAPISemantics.upd_SigmaAPI None RealSemMT.st; (* resets call *)
                                    }
      end;
      }        
    }
    return r;
  }
}.

section MTSecurityProof.

declare module A: Adversary{ProgSem, ProgSem, AdvOrclMT}.
declare module Z: Environment{A, API_Real, ProgSem, AdvOrclMT}.

op inv (stMT1 stMT2: Target.MultiPartyAPISemantics.GlobalSt) (stST2: Source.MultiPartyAPISemantics.GlobalSt) =
 stMT2.`Target.MultiPartyAPISemantics.StP1 = stMT1.`Target.MultiPartyAPISemantics.StP1 /\
 stMT2.`Target.MultiPartyAPISemantics.StP2 = stMT1.`Target.MultiPartyAPISemantics.StP2 /\
 stMT2.`Target.MultiPartyAPISemantics.StP3 = stMT1.`Target.MultiPartyAPISemantics.StP3 /\
 Source.MultiPartyAPISemantics.ib stST2 = stMT1.`Target.MultiPartyAPISemantics.ib /\
 Source.MultiPartyAPISemantics.ob stST2 = stMT1.`Target.MultiPartyAPISemantics.ob /\
 Source.MultiPartyAPISemantics.StP1 stST2 = Source.MultiPartyAPISemantics.StP2 stST2 /\
  Source.MultiPartyAPISemantics.StP2 stST2 = Source.MultiPartyAPISemantics.StP3 stST2 /\
 advSt1 Target.MultiPartyAPISemantics.SemP1.stepL (Source.MultiPartyAPISemantics.StP1 stST2) stMT1.`Target.MultiPartyAPISemantics.StP1 /\
 advSt2 Target.MultiPartyAPISemantics.SemP2.stepL (Source.MultiPartyAPISemantics.StP2 stST2) stMT1.`Target.MultiPartyAPISemantics.StP2 /\
 advSt3 Target.MultiPartyAPISemantics.SemP3.stepL (Source.MultiPartyAPISemantics.StP3 stST2) stMT1.`Target.MultiPartyAPISemantics.StP3.

local lemma nosmt stepP_prop:
 equiv [ RealSemMT.stepP ~ AdvOrclMT(RealSem).stepP:
         ={id} /\ ={API_Real.senv} /\
         inv Target.ProgSem.st{1} Target.ProgSem.st{2} Source.ProgSem.st{2}
         ==>
         ={res} /\ ={API_Real.senv} /\
         inv Target.ProgSem.st{1} Target.ProgSem.st{2} Source.ProgSem.st{2} ].
proof.
proc.
sp.
match => //=.
if => //=.
smt().
sp 1 1.
if => //=.
smt().
wp; skip; rewrite /inv; progress.
- smt(). smt(). smt(). smt(). smt(). smt(). smt().
- move: H6 => [??[?[??]]].
exists (n+1) st'; progress; rewrite /upd_Sigma1 /=; first smt().
  apply: (Target.MultiPartyAPISemantics.SemP1.stepPiterS_some _ _ _ _ _ _ H12) => //=.
  by rewrite -some_oget //.
smt(). smt().

if => //=.
smt().
sp 1 1.
if => //=.
smt().
wp; skip; rewrite /inv; progress.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
- move: H7 => [??[?[??]]].
exists (n+1) st'; progress; rewrite /upd_Sigma2 /=; first smt().
  apply: (Target.MultiPartyAPISemantics.SemP2.stepPiterS_some _ _ _ _ _ _ H12) => //=.
  by rewrite -some_oget //.
smt(). 

if => //=.
smt().
sp 1 1.
if => //=.
smt().
wp; skip; rewrite /inv; progress.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
- move: H8 => [??[?[??]]].
exists (n+1) st'; progress; rewrite /upd_Sigma3 /=; first smt().
  apply: (Target.MultiPartyAPISemantics.SemP3.stepPiterS_some _ _ _ _ _ _ H12) => //=.
  by rewrite -some_oget //.
qed.

lemma local_source_step12 : Source.MultiPartyAPISemantics.SemP1.stepL = Source.MultiPartyAPISemantics.SemP2.stepL.
proof.
rewrite fun_ext /(==) => ? /#.
qed.

lemma test k i f ss :
  0 <= i =>
  0 <= k =>
  i < k =>
  SemP1.stepPiter f k ss <> None =>
  SemP1.stepPiter f i ss <> None.
proof.
move => ?.
elim k.
simplify.
move => /> *.
smt.
move => /> k *.
move : H3.
rewrite SemP1.stepPiterS.
smt().
move => *.
smt.
qed.


local lemma nosmt stepS_prop:
 equiv [ RealSemMT.stepS ~ AdvOrclMT(RealSem).stepS:
         true /\ ={API_Real.senv} /\
         inv Target.ProgSem.st{1} Target.ProgSem.st{2} Source.ProgSem.st{2}
         ==>
         ={res} /\ ={API_Real.senv} /\
         inv Target.ProgSem.st{1} Target.ProgSem.st{2} Source.ProgSem.st{2} ].
proof.
proc.
sp 2 2; simplify.
if; [smt() | | by skip; progress].
seq 0 0: ((exists (ks : int) ss',
            (*stepPiter stepL ks (oget ProgSem.st{2}.`Sigma.[1])*)
            Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL ks (Source.MultiPartyAPISemantics.StP1 Source.ProgSem.st{2})
            = Some ss' /\
            equivSt1 ss' Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP1 /\ 0 <= ks)
          /\ #[/:]pre).
 skip; rewrite /inv => |> *.
 move: H6 => [??[?[??]]].
 apply (bisim_backward1 _ _ _ _ H10 H11 _); smt(). 
elim* => ??.
exists* (Source.MultiPartyAPISemantics.StP1 Source.ProgSem.st{2}); elim* => ss.
conseq (_: ss = Source.MultiPartyAPISemantics.StP1 Source.ProgSem.st{2} /\
           Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL ks (Source.MultiPartyAPISemantics.StP1 Source.ProgSem.st{2}) = Some ss' /\
           equivSt1 ss' Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP1 /\
           equivSt2 ss' Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP2 /\
           equivSt3 ss' Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP3 /\
           ={r,ecall,API_Real.senv} /\
           0 <= ks /\ r{2}=None /\
           ecall{2} = Target.MultiPartyAPISemantics.SemP1.callSt Target.ProgSem.st{2}.`Target.MultiPartyAPISemantics.StP1 /\
           ecall{2} = Target.MultiPartyAPISemantics.SemP2.callSt Target.ProgSem.st{2}.`Target.MultiPartyAPISemantics.StP2 /\
           ecall{2} = Target.MultiPartyAPISemantics.SemP3.callSt Target.ProgSem.st{2}.`Target.MultiPartyAPISemantics.StP3 /\
           ecall{2} <> None /\
           Target.ProgSem.st{2}.`Target.MultiPartyAPISemantics.StP1 = Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP1 /\
           Target.ProgSem.st{2}.`Target.MultiPartyAPISemantics.StP2 = Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP2 /\
           Target.ProgSem.st{2}.`Target.MultiPartyAPISemantics.StP3 = Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.StP3 /\
           Source.MultiPartyAPISemantics.ib Source.ProgSem.st{2} = Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.ib /\
           Source.MultiPartyAPISemantics.ob Source.ProgSem.st{2} = Target.ProgSem.st{1}.`Target.MultiPartyAPISemantics.ob /\
           Source.MultiPartyAPISemantics.StP1 Source.ProgSem.st{2} = Source.MultiPartyAPISemantics.StP2 Source.ProgSem.st{2} /\
           Source.MultiPartyAPISemantics.StP2 Source.ProgSem.st{2} = Source.MultiPartyAPISemantics.StP3 Source.ProgSem.st{2}
           ==> _).
 rewrite /inv => |> *; auto.
 split; [|split; [|smt()]].
  move: H10 => [??[?[??]]].
  move: (bisim_backward2 _ _ _ _ H13 H14 _); first smt().
  move=> [??] [?[??]].

have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL ks0
        Source.ProgSem.st{2}.`Source.MultiPartyAPISemantics.StP1 = Some ss'0.
rewrite -H15.
cut ->: Source.MultiPartyAPISemantics.SemP1.stepL = Source.MultiPartyAPISemantics.SemP2.stepL.
rewrite fun_ext /(==) => *.
smt().
rewrite H7.
done.

  have ?:= (Source.MultiPartyAPISemantics.SemP2.stepPiter_det _ _ _ _ _ _ _ _ H _ H18 _); first 4 smt().
  by move: H18; rewrite -H19 H; move => /#.
 move: H11 => [??[?[??]]].
 move: (bisim_backward3 _ _ _ _ H13 H14 _); first smt().
 move=> [??] [?[??]].

have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL ks0
        Source.ProgSem.st{2}.`Source.MultiPartyAPISemantics.StP1 = Some ss'0.
rewrite -H15.
cut ->: Source.MultiPartyAPISemantics.SemP1.stepL = Source.MultiPartyAPISemantics.SemP3.stepL.
rewrite fun_ext /(==) => *.
smt().
rewrite H7 H8.
done.

 have ?:= (Source.MultiPartyAPISemantics.SemP3.stepPiter_det _ _ _ _ _ _ _ _ H _ H18 _); first 4 smt().
 by move: H18; rewrite -H19 H; move => /#.

seq 0 3: (ss' = Source.ProgSem.st{2}.`Source.MultiPartyAPISemantics.StP1 /\
          #[/3:]pre).          
 sp 0 2.
 while {2} ((b = (i <= ks)){2} /\
             0 <= i{2} <= ks+1 /\ 
             (Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL ks ss = Some ss') /\
             (oget (Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL (i+b2i b-1) ss) = Source.ProgSem.st{2}.`Source.MultiPartyAPISemantics.StP1){2} /\
             #[/5:]pre
            ) (ks+1-i{2}).
   move=> *; exlim Source.ProgSem.st => sw.
   case (i = ks).
    wp; call (stepP_spec P3 sw).
    call (stepP_spec P2 sw). 
    call (stepP_spec P1 sw).
    skip=> *.
    have Hloop: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 (Source.ProgSem.st{hr}.`Source.MultiPartyAPISemantics.StP1)
                = None.
     move: H; progress.
     move: H2; rewrite H17 b2i1 /= H1 => <- /=.
     by move: (Source.MultiPartyAPISemantics.SemP1.callSt_stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 ss' _); smt().
    move: H; rewrite /inv;
progress.
smt(Source.MultiPartyAPISemantics.SemP1.stepPiter0 get_set_id).
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP2.stepPiter Source.MultiPartyAPISemantics.SemP2.stepL 1 Source.ProgSem.st{hr}.`StP2.
cut ->: Source.MultiPartyAPISemantics.SemP2.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt(-local_source_step12).
rewrite H15.
rewrite /stepPiter.
congr.
have hloop2 : Source.MultiPartyAPISemantics.SemP2.stepPiter Source.MultiPartyAPISemantics.SemP2.stepL 1 Source.ProgSem.st{hr}.`StP2 = None.
smt().
rewrite hloop2.
rewrite /b2i /=.
smt(Source.MultiPartyAPISemantics.SemP2.stepPiter0 get_set_id).
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3.
cut ->: Source.MultiPartyAPISemantics.SemP3.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt().
rewrite H15 H16.
rewrite /stepPiter.
congr.
have hloop3 : Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3 = None.
smt().
rewrite hloop3.
rewrite /b2i /=.
smt(Source.MultiPartyAPISemantics.SemP3.stepPiter0 get_set_id).
smt().
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3.
cut ->: Source.MultiPartyAPISemantics.SemP3.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt().
rewrite H15 H16.
rewrite /stepPiter.
congr.
have hloop3 : Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3 = None.
smt().
rewrite hloop3.
rewrite /b2i /=.
smt(Source.MultiPartyAPISemantics.SemP3.stepPiter0 get_set_id).
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3.
cut ->: Source.MultiPartyAPISemantics.SemP3.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt().
rewrite H15 H16.
rewrite /stepPiter.
congr.
have hloop3 : Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3 = None.
smt().
rewrite hloop3.
rewrite /b2i /=.
smt(Source.MultiPartyAPISemantics.SemP3.stepPiter0 get_set_id).
smt(). 

   wp; call (stepP_spec P3
    {| sw with StP1 = oget (SemP1.stepPiter SemP1.stepL 1 sw.`StP1) ;
              StP2 = oget (SemP2.stepPiter SemP2.stepL 1 sw.`StP2) |}).
   call (stepP_spec P2 {| sw with StP1 = oget (SemP1.stepPiter SemP1.stepL 1 sw.`StP1) |}). 
   call (stepP_spec P1 sw).
   skip => *. 
    have Hloop: SemP1.stepPiter SemP1.stepL 1 (Source.ProgSem.st{hr}.`StP1)
                <> None.
    apply (SemP1.stepPiter_lt _ ks i{hr} ss); first 2 smt().
     move: H; progress.
     move: H2; rewrite H17 b2i1 /=.

move => <-.
rewrite -some_oget.
smt(test).
done.

move: H; rewrite /inv;
progress.
smt(Source.MultiPartyAPISemantics.SemP1.stepPiter0 get_set_id).
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP2.stepPiter Source.MultiPartyAPISemantics.SemP2.stepL 1 Source.ProgSem.st{hr}.`StP2.
cut ->: Source.MultiPartyAPISemantics.SemP2.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt(-local_source_step12).
rewrite H15.
rewrite /stepPiter.
congr.
smt().
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3.
cut ->: Source.MultiPartyAPISemantics.SemP3.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt().
rewrite H15 H16.
rewrite /stepPiter.
congr.
smt().
smt().
smt().
rewrite /b2i /=.
have ?: Source.MultiPartyAPISemantics.SemP1.stepPiter Source.MultiPartyAPISemantics.SemP1.stepL 1 Source.ProgSem.st{hr}.`StP1 = Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3.
cut ->: Source.MultiPartyAPISemantics.SemP3.stepL = Source.MultiPartyAPISemantics.SemP1.stepL.
smt().
rewrite H15 H16.
rewrite /stepPiter.
congr.
simplify.
have hloop3 : Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3 <> None.
smt().
rewrite hloop3.
rewrite /b2i /=.
move : H2.
rewrite /b2i H17 /=.
move => *.
rewrite SemP1.stepPiterS 1:/#.
cut -> : SemP1.stepPiter SemP1.stepL i{hr} ss = Some (Source.ProgSem.st{hr}.`StP1).
smt(test).
smt().
rewrite H15 H16.
rewrite /stepPiter.
congr.

rewrite H16.
congr.
simplify.
rewrite /b2i /=.
have hloop3 : Source.MultiPartyAPISemantics.SemP3.stepPiter Source.MultiPartyAPISemantics.SemP3.stepL 1 Source.ProgSem.st{hr}.`StP3 <> None.
have ? : SemP1.stepPiter SemP1.stepL i{hr} ss = Some (Source.ProgSem.st{hr}.`StP1).
smt(test).
cut ->: SemP3.stepPiter = SemP1.stepPiter. smt().
cut ->: SemP3.stepL = SemP1.stepL. smt().
cut ->: Source.ProgSem.st{hr}.`StP3 = Source.ProgSem.st{hr}.`StP1. smt().
smt().
rewrite hloop3 /=.
cut ->: SemP3.stepPiter = SemP1.stepPiter. smt().
cut ->: SemP3.stepL = SemP1.stepL. smt().
done.

smt().

 skip; progress; 1..2,4..5: smt().
 by rewrite b2i1 /= SemP1.stepPiter0 // -some_oget /#.

inline Source.ProgSem(API_Real).stepS.
seq 0 2: (#[/:]pre /\ r0{2} = None /\ ecall{1}=ecall0{2}).
 wp; skip; rewrite /inv; progress.
 rewrite /allECalls => /#.
rcondt {2} 1; first by move=>*; skip; progress.
match; move=> *. 
- (* call_declass *)
  split; move => [a Ha]; exists a; smt().
- (* call_in *)
  split; move => [a Ha]; exists a; smt().
- (* call_out *)
  split; move => [a Ha]; exists a; smt().
- (* call_sop *)
  split; move => [o a pargs sargs Ho]; exists o a pargs sargs; smt().


- (* call_declass *)
inline*.
sp; (if; first by smt()); last first.
wp. wp; skip; progress.
smt. smt. smt.
wp; rnd; wp; skip; progress.
smt().
smt().
rewrite H /=.
rewrite /upd_SigmaAPI /updRes /=.

rewrite /inv => |>*; progress. 
smt(prot_declass_suppE).
smt().
smt(prot_declass_suppE).
smt().
smt(prot_declass_suppE).
smt().
smt().
smt().
smt.
smt.
smt.
    
- (* call_in *)
  if => //=; [smt() | |]; last first.
   rcondf {2} 2; first by move=>*; wp; skip; progress.
   wp; skip; progress. smt. smt. smt.
  seq 1 1: (#pre /\ ={ato}).
   call (_: ={API_Real.senv} /\ a{1}=a0{2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
(if; first by smt()); last first.
sp 0 1; if{2}; first by exfalso => /#.
skip; progress.
smt. smt. smt.
rcondt{2} 6; first by move => *; wp; skip.

  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /= /#. 
    - by rewrite /upd_SigmaAPI /= /#.
smt. 
smt.
smt.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
- (* call_out *)
  if => //=; [smt() | |]; last first.
   rcondf {2} 2; first by move=>*; wp; skip; progress.
   wp; skip; progress. smt. smt. smt.
  seq 1 1: (#pre /\ ={xto}).
   call (_: ={API_Real.senv} /\ a{1}=a0{2}).
sp. if; last by skip. smt().
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
(if; first by smt()); last first.
sp 0 1; if{2}; first by exfalso => /#.
skip; progress.
smt. smt. smt.
rcondt{2} 6; first by move => *; wp; skip.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /upd_P_API /upd_obmt /= /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= /= /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= /#.
smt.
smt.
smt.
  + wp; skip; progress; smt().
- (* call_sop *)
  seq 1 1: (#pre /\ ={ato}).
   call (_: ={API_Real.senv} /\
            (o,pargs,sargs,a){1}=(o0,pargs0,sargs0,a0){2}).
sp; (if; first by smt()); last by skip.    
by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
(if; first by smt()); last first.
sp 0 1; if{2}; first by exfalso => /#.
skip; progress.
smt. smt. smt.
rcondt{2} 5; first by move => *; wp; skip.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /=/updRes /#. 
    - by rewrite /upd_SigmaAPI /=/updRes /#. 
smt.
smt.
smt.
qed.

equiv SecurityMT:
 Eval(RealSem,Z,A).eval ~ REAL(Z, AdvMT(A)).game
 : ={P, glob A, glob Z} ==> ={res}.
proof.
proc.
call (_: ={glob A, API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
     ). 
- (* setInput *)
  by proc; inline*; wp; skip; progress; smt().
- (* getOutput *)
  by proc; inline*; wp; skip; progress; smt().
- (* activate *)
  proc; call (_: ={API_Real.senv} /\
                 inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
             ).
  + (* stepP *)
    by apply stepP_prop.
  + (* stepS *)
    by apply stepS_prop.
    by skip; progress. 
- inline*; call (_: ={API_Real.senv} /\
                    inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
                ).
  by apply stepP_prop.
 by apply stepS_prop.
wp; skip => /> *; progress.
- rewrite /init_GlobalSt /= (_:3=1+1+1) 1:// !iotaS //= iota1 /=;
  smt(get_setE).
- rewrite /init_GlobalSt /= (_:3=1+1+1) 1:// !iotaS //= iota1 /=;
  smt(get_setE).
- rewrite /init_GlobalSt /= (_:3=1+1+1) 1:// !iotaS //= iota1 /=;
  smt(get_setE).
- rewrite /advStT; exists 0 (init_GlobalMTSt P{2}).`P1.
  split; first done.
  split; last by rewrite stepPiter0.
  have ?:= (equivSt_init1 P{2}).
  rewrite /init_GlobalSt /=  (_:3=1+1+1) 1:// !iotaS //= iota1 /=.
  by rewrite !get_setE /#.
- rewrite /advStT; exists 0 (init_GlobalMTSt P{2}).`P2.
  split; first done.
  split; last by rewrite stepPiter0.
  have ?:= (equivSt_init2 P{2}).
  rewrite /init_GlobalSt /=  (_:3=1+1+1) 1:// !iotaS //= iota1 /=.
  by rewrite !get_setE /#.
- rewrite /advStT; exists 0 (init_GlobalMTSt P{2}).`P3.
  split; first done.
  split; last by rewrite stepPiter0.
  have ?:= (equivSt_init3 P{2}).
  rewrite /init_GlobalSt /=  (_:3=1+1+1) 1:// !iotaS //= iota1 /=.
  by rewrite !get_setE /#.
qed.



equiv SecurityMT:
 REAL_MT(Z, A).game ~ REAL(Z, AdvMT(A)).game
 : ={P, glob A, glob Z} ==> ={res}.
proof.
proc.
call (_: ={glob A, API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
     ). 
- (* setInput *)
  by proc; inline*; wp; skip; progress; smt().
- (* getOutput *)
  by proc; inline*; wp; skip; progress; smt().
- (* activate *)
  proc; call (_: ={API_Real.senv} /\
                 inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
             ).
  + (* stepP *)
    by apply stepP_prop.
  + (* stepS *)
    by apply stepS_prop.
    by skip; progress. 
- inline*; call (_: ={API_Real.senv} /\
                    inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
                ).
  by apply stepP_prop.
 by apply stepS_prop.
wp; skip => /> *; progress.
- rewrite /init_GlobalSt /= (_:3=1+1+1) 1:// !iotaS //= iota1 /=;
  smt(get_setE).
- rewrite /init_GlobalSt /= (_:3=1+1+1) 1:// !iotaS //= iota1 /=;
  smt(get_setE).
- rewrite /init_GlobalSt /= (_:3=1+1+1) 1:// !iotaS //= iota1 /=;
  smt(get_setE).
- rewrite /advStT; exists 0 (init_GlobalMTSt P{2}).`P1.
  split; first done.
  split; last by rewrite stepPiter0.
  have ?:= (equivSt_init1 P{2}).
  rewrite /init_GlobalSt /=  (_:3=1+1+1) 1:// !iotaS //= iota1 /=.
  by rewrite !get_setE /#.
- rewrite /advStT; exists 0 (init_GlobalMTSt P{2}).`P2.
  split; first done.
  split; last by rewrite stepPiter0.
  have ?:= (equivSt_init2 P{2}).
  rewrite /init_GlobalSt /=  (_:3=1+1+1) 1:// !iotaS //= iota1 /=.
  by rewrite !get_setE /#.
- rewrite /advStT; exists 0 (init_GlobalMTSt P{2}).`P3.
  split; first done.
  split; last by rewrite stepPiter0.
  have ?:= (equivSt_init3 P{2}).
  rewrite /init_GlobalSt /=  (_:3=1+1+1) 1:// !iotaS //= iota1 /=.
  by rewrite !get_setE /#.
qed.

end section MTSecurityProof.

