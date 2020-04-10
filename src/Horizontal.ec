require import AllCore List SmtMap Distr IntExtra IntDiv DMap FSet.

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
 type L3.L = L.

clone import Language as L1'.
clone import Language as L2'.
clone import Language as L3'.

clone import MultiPartyProtocolAPISemantics as Target with
  type L1.L = L1'.L,
  type L2.L = L2'.L,
  type L3.L = L3'.L.
import MultiPartyAPISemantics.

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

(** COMPILERS **)

(* Compiler Correctness *)

(* equivalence relation on source/target local states *)
op equivLSt ['ls, 'es, 'lt, 'et] : ('ls*'es) -> ('lt*'et) -> bool.

print SemP1.API.apiCallRes.
print API.apiCallRes.
print ProtocolAPI.API.apiCallRes.
print apiCallRes.

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
op advSt1 ['l,'e] step (ss: (L,Source.MultiPartyAPISemantics.SemP1.EnvL) Source.MultiPartyAPISemantics.SemP1.APIst) (st: ('l,'e) Target.MultiPartyAPISemantics.SemP1.APIst) : bool =
 exists n st', 0 <= n /\ equivSt1 ss st' /\ Target.MultiPartyAPISemantics.SemP1.stepPiter step n st' = Some st.

lemma advS01 ['l, 'e] step s1 (s2: ('l, 'e) Target.MultiPartyAPISemantics.SemP1.APIst):
 equivSt1 s1 s2 => advSt1 step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite Target.MultiPartyAPISemantics.SemP1.stepPiter0.
qed.

lemma nosmt advSt_callSt1 ['l, 'e] step s1 (s2: ('l, 'e) Target.MultiPartyAPISemantics.SemP1.APIst):
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

op advSt2 ['l,'e] step (ss: (L,Source.MultiPartyAPISemantics.SemP2.EnvL) Source.MultiPartyAPISemantics.SemP2.APIst) (st: ('l,'e) Target.MultiPartyAPISemantics.SemP2.APIst) : bool =
 exists n st', 0 <= n /\ equivSt2 ss st' /\ Target.MultiPartyAPISemantics.SemP2.stepPiter step n st' = Some st.

lemma advS02 ['l, 'e] step s1 (s2: ('l, 'e) Target.MultiPartyAPISemantics.SemP2.APIst):
 equivSt1 s1 s2 => advSt1 step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite Target.MultiPartyAPISemantics.SemP2.stepPiter0.
qed.

lemma nosmt advSt_callSt2 ['l, 'e] step s1 (s2: ('l, 'e) Target.MultiPartyAPISemantics.SemP2.APIst):
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

op advSt3 ['l,'e] step (ss: (L,Source.MultiPartyAPISemantics.SemP3.EnvL) Source.MultiPartyAPISemantics.SemP3.APIst) (st: ('l,'e) Target.MultiPartyAPISemantics.SemP3.APIst) : bool =
 exists n st', 0 <= n /\ equivSt3 ss st' /\ Target.MultiPartyAPISemantics.SemP3.stepPiter step n st' = Some st.

lemma advS03 ['l, 'e] step s1 (s2: ('l, 'e) Target.MultiPartyAPISemantics.SemP3.APIst):
 equivSt3 s1 s2 => advSt3 step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite Target.MultiPartyAPISemantics.SemP3.stepPiter0.
qed.

lemma nosmt advSt_callSt3 ['l, 'e] step s1 (s2: ('l, 'e) Target.MultiPartyAPISemantics.SemP3.APIst):
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

(*module RealSemMT: RealSemInterface = {
  module PSem = ProgSemMT(API_Real)
  include PSem
}.*)

module RealSemMT = Target.ProgSem(API_Real).

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
    var ecall <- Target.syncPoint (Target.MultiPartyAPISemantics.SemP1.callSt (StP1 SemEmu.st),
                            Target.MultiPartyAPISemantics.SemP2.callSt (StP2 SemEmu.st),
                            Target.MultiPartyAPISemantics.SemP3.callSt (StP3 SemEmu.st));
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
                                RealSemMT.st <- upd_SigmaAPI (Some (oget v)) RealSemMT.st;
                              }
          | Call_in a => { RealSemMT.st <- upd_SigmaAPI None RealSemMT.st; (* resets call *)
                         }
          | Call_out a => { RealSemMT.st <- upd_SigmaAPI None RealSemMT.st; (* resets call *)
                          }
      | Call_sop o a pargs sargs => { RealSemMT.st <- upd_SigmaAPI None RealSemMT.st; (* resets call *)
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

op inv (stMT1 stMT2: GlobalMTSt) (stST2: GlobalSt) =
 stMT2.`P1 = stMT1.`P1 /\
 stMT2.`P2 = stMT1.`P2 /\
 stMT2.`P3 = stMT1.`P3 /\
 stST2.`ib = stMT1.`ibmt /\
 stST2.`ob = stMT1.`obmt /\
 stST2.`Sigma.[1] <> None /\
 stST2.`Sigma.[2] = stST2.`Sigma.[1] /\
 stST2.`Sigma.[3] = stST2.`Sigma.[1] /\
 advSt stepL1 (oget stST2.`Sigma.[1]) stMT1.`P1 /\
 advSt stepL2 (oget stST2.`Sigma.[1]) stMT1.`P2 /\
 advSt stepL3 (oget stST2.`Sigma.[1]) stMT1.`P3.

local lemma nosmt stepP_prop:
 equiv [ RealSemMT.stepP ~ AdvOrclMT(RealSem).stepP:
         ={id} /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
         ==>
         ={res} /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2} ].
proof.
proc; wp; skip; rewrite /inv; progress.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
- move: H7 => [??[?[??]]].
  exists (n+1) st'; progress; rewrite /upd_P1 /=; first smt().
  apply: (stepPiterS_some _ _ _ _ _ _ H15) => //=.
  by rewrite -some_oget //.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
  smt(). smt(). smt().
- move: H8 => [??[?[??]]].
  exists (n+1) st'; progress; rewrite /upd_P2 /=; first smt().
  apply: (stepPiterS_some _ _ _ _ _ _ H16) => //=.
  by rewrite -some_oget //.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
  smt(). smt(). smt().
- move: H9 => [??[?[??]]].
  exists (n+1) st'; progress; rewrite /upd_P3 /=; first smt().
  apply: (stepPiterS_some _ _ _ _ _ _ H17) => //=.
  by rewrite -some_oget //.
- smt(). smt(). smt().
qed.

local lemma nosmt stepS_prop:
 equiv [ RealSemMT.stepS ~ AdvOrclMT(RealSem).stepS:
         true /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
         ==>
         ={res} /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2} ].
proof.
proc.
sp 2 2; simplify.
if; [smt() | | by skip; progress].
seq 0 0: ((exists ks ss',
            stepPiter stepL ks (oget ProgSem.st{2}.`Sigma.[1])
            = Some ss' /\
            equivSt ss' ProgSemMT.st{1}.`P1 /\ 0 <= ks)
          /\ #[/:]pre).
 skip; rewrite /inv => |> *.
 move: H7 => [??[?[??]]].
 apply (bisim_backward1 _ _ _ _ H11 H12 _); smt(). 
elim* => ??.
exists* (oget ProgSem.st{2}.`Sigma.[1]); elim* => ss.
conseq (_: ss = oget ProgSem.st{2}.`Sigma.[1] /\
           stepPiter stepL ks ss = Some ss' /\
           equivSt ss' ProgSemMT.st{1}.`P1 /\
           equivSt ss' ProgSemMT.st{1}.`P2 /\
           equivSt ss' ProgSemMT.st{1}.`P3 /\
           ={r,ecall,API_Real.senv} /\
           0 <= ks /\ r{2}=None /\
           ecall{2} = callSt ProgSemMT.st{2}.`P1 /\
           ecall{2} = callSt ProgSemMT.st{2}.`P2 /\
           ecall{2} = callSt ProgSemMT.st{2}.`P3 /\
           ecall{2} <> None /\
           ProgSemMT.st{2}.`P1 = ProgSemMT.st{1}.`P1 /\
           ProgSemMT.st{2}.`P2 = ProgSemMT.st{1}.`P2 /\
           ProgSemMT.st{2}.`P3 = ProgSemMT.st{1}.`P3 /\
           ProgSem.st{2}.`ib = ProgSemMT.st{1}.`ibmt /\
           ProgSem.st{2}.`ob = ProgSemMT.st{1}.`obmt /\
           ProgSem.st{2}.`Sigma.[1] <> None /\
           ProgSem.st{2}.`Sigma.[2] = ProgSem.st{2}.`Sigma.[1] /\
           ProgSem.st{2}.`Sigma.[3] = ProgSem.st{2}.`Sigma.[1]
           ==> _).
 rewrite /inv => |> *; auto.
 split; [|split; [|smt()]].
  move: H11 => [??[?[??]]].
  move: (bisim_backward2 _ _ _ _ H14 H15 _); first smt().
  move=> [??] [?[??]].
  have ?:= (stepPiter_det _ _ _ _ _ _ _ _ H _ H16 _); first 4 smt().
  by move: H16; rewrite -H19 H; move => /#.
 move: H12 => [??[?[??]]].
 move: (bisim_backward3 _ _ _ _ H14 H15 _); first smt().
 move=> [??] [?[??]].
 have ?:= (stepPiter_det _ _ _ _ _ _ _ _ H _ H16 _); first 4 smt().
 by move: H16; rewrite -H19 H; move => /#.
seq 0 3: (ss' = (oget ProgSem.st{2}.`Sigma.[1]) /\
          #[/3:]pre).          
 sp 0 2.
 while {2} ((b = (i <= ks)){2} /\
             0 <= i{2} <= ks+1 /\ 
             (stepPiter stepL ks ss = Some ss') /\
             (stepPiter stepL (i+b2i b-1) ss = ProgSem.st{2}.`Sigma.[1]){2} /\
             #[/5:]pre
            ) (ks+1-i{2}).
   move=> *; exlim ProgSem.st => sw.
   case (i = ks).
    wp; call (stepP_spec 3 sw).
    call (stepP_spec 2 sw). 
    call (stepP_spec 1 sw).
    skip=> *.
    have Hloop: stepPiter stepL 1 (oget ProgSem.st{hr}.`Sigma.[1])
                = None.
     move: H; progress.
     move: H2; rewrite H18 b2i1 /= H1 => <- /=.
     by move: (callSt_stepPiter stepL 1 ss' _); smt().
    move: H; rewrite /inv;
    progress; 1..6,8..: smt(stepPiter0 get_set_id).
    - rewrite !H17 Hloop b2i0 /=; smt(get_setE).
   wp; call (stepP_spec 3 
    {| sw with Sigma = sw.`Sigma.[
        1 <- oget (stepPiter stepL 1 (oget (sw.`Sigma.[1])))].[
        2 <- oget (stepPiter stepL 1 (oget (sw.`Sigma.[1])))] |}).
   call (stepP_spec 2 {| sw with Sigma = sw.`Sigma.[
        1 <- oget (stepPiter stepL 1 (oget (sw.`Sigma.[1])))] |}). 
   call (stepP_spec 1 sw).
   skip => *.
   have Hloop: stepPiter stepL 1 (oget ProgSem.st{hr}.`Sigma.[1])
               <> None.
    apply (stepPiter_lt _ ks i{hr} ss); first 2 smt().
    rewrite -some_oget 1:/#.
    move: H; progress; smt().
   move: H; rewrite /inv; progress; 1..7,9..12: smt(get_setE).
   - rewrite !get_setE /=.
     rewrite H17 Hloop b2i1 /= -some_oget //.
     rewrite stepPiterS; first smt().
     move: H2; rewrite H18 b2i1 /= => ->.
     by rewrite (some_oget ProgSem.st{hr}.`Sigma.[1]) /#.
 skip; progress; 1..2,4..5: smt().
 by rewrite b2i1 /= stepPiter0 // -some_oget /#.
inline RealSem.stepS.
seq 0 2: (#[/:]pre /\ r0{2} = None /\ ecall{1}=ecall0{2}).
 wp; skip; rewrite /inv; progress.
 rewrite /allECalls (_:3 = 1+1+1) 1:// !iotaS // iota1 /=.
 by rewrite !H12 !H13 /= H3 (equivSt_callSt _ _ H) /#.
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
  inline API_Real.api_declass.
  rcondt {2} 7.
   move=> *; inline*; wp; rnd; wp; skip; progress; smt().
  inline*; sp.
  seq 1 1: (#pre /\ ={t0}); first by rnd; skip; progress; smt().
  sp; match {2}.
  + move=> *; wp; skip; progress; first 5 smt().
    - by rewrite /upd_SigmaAPI /= mapE /= /updRes /upd_ib /=
                 (some_oget st_R.`Sigma.[1]) // /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - exists 0 (upd_P_API (Some (oget (leakage_value (oget t0{2}.`leakage)))) st_L).`P1.
      split; first done.
      split; last by apply stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_SigmaAPI
                 /= mapE /= /updRes /= oget_omap_some /#.
    - exists 0 (upd_P_API (Some (oget (leakage_value (oget t0{2}.`leakage)))) st_L).`P2.
      split; first done.
      split; last by apply stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_SigmaAPI
                 /= mapE /= /updRes /= oget_omap_some /#.
    - exists 0 (upd_P_API (Some (oget (leakage_value (oget t0{2}.`leakage)))) st_L).`P3.
      split; first done.
      split; last by apply stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_SigmaAPI
                 /= mapE /= /updRes /= oget_omap_some /#.
  + move=> *; wp; skip; progress; smt().
  + move=> *; wp; skip; progress; smt().
  + move=> *; wp; skip; progress; smt().
- (* call_in *)
  if => //=; [smt() | |]; last first.
   rcondf {2} 2; first by move=>*; wp; skip; progress.
   by wp; skip; progress; smt(advSt0).
  seq 1 1: (#pre /\ ={t}).
   call (_: ={API_Real.senv} /\ a{1}=a0{2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
  rcondt {2} 5; first by move=>*; wp; skip; progress.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /= mapE /= /updRes /upd_ib /=
                 (some_oget st_R.`Sigma.[1]) // /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P1.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P2.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P3.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
- (* call_out *)
  if => //=; [smt() | |]; last first.
   rcondf {2} 2; first by move=>*; wp; skip; progress.
   by wp; skip; progress; smt(advSt0).
  seq 1 1: (#pre /\ ={x, t}).
   call (_: ={API_Real.senv} /\ a{1}=a0{2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
  rcondt {2} 5; first by move=>*; wp; skip; progress.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /upd_P_API /upd_obmt /= mapE /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= !mapE /= /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P1.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P2.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P3.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
  + wp; skip; progress; smt().
- (* call_sop *)
  seq 1 1: (#pre /\ ={t}).
   call (_: ={API_Real.senv} /\
            (o,pargs,sargs,a){1}=(o0,pargs0,sargs0,a0){2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt(advSt0).
  rcondt {2} 4; first by move=>*; wp; skip; progress.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - rewrite /upd_SigmaAPI /= mapE /= /updRes /upd_ib /=
              (some_oget st_R.`Sigma.[1]) // /#.
    - by rewrite /upd_SigmaAPI /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /= !mapE /= /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P1.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P2.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P3.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
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























end Compilation.



theory MultiThreaded.

clone import SingleThreaded as ST with op n_parties <- 3, op n_corrupted <- 3.

(* Target Languages *)

(* Programs *)
type L1.
type L2.
type L3.

(* Environment *)
type EnvL1.
type EnvL2.
type EnvL3.

(* initial state *)
op initStateL1 (P:L1): L1*EnvL1.
op initStateL2 (P:L2): L2*EnvL2.
op initStateL3 (P:L3): L3*EnvL3.

type StateL1 = (L1, EnvL1) APIst.
type StateL2 = (L2, EnvL2) APIst.
type StateL3 = (L3, EnvL3) APIst.

(* (local) Step semantics *)
op stepL1 : L1 -> EnvL1 -> apiRes_data option -> ((L1,EnvL1) ECall) option.
op stepL2 : L2 -> EnvL2 -> apiRes_data option -> ((L2,EnvL2) ECall) option.
op stepL3 : L3 -> EnvL3 -> apiRes_data option -> ((L3,EnvL3) ECall) option.


(* ASSUMPTION: backward simulation (trace preservation) *)
axiom bisim_backward1 ss st kt st':
 equivSt ss st =>
 stepPiter stepL1 kt st = Some st' =>
 callSt st' <> None =>
 (exists ks ss', stepPiter stepL ks ss = Some ss'
                 /\ equivSt ss' st' /\ 0 <= ks).

axiom bisim_backward2 ss st kt st':
 equivSt ss st =>
 stepPiter stepL2 kt st = Some st' =>
 callSt st' <> None =>
 (exists ks ss', stepPiter stepL ks ss = Some ss'
                 /\ equivSt ss' st' /\ 0 <= ks).

axiom bisim_backward3 ss st kt st':
 equivSt ss st =>
 stepPiter stepL3 kt st = Some st' =>
 callSt st' <> None =>
 (exists ks ss', stepPiter stepL ks ss = Some ss'
                 /\ equivSt ss' st' /\ 0 <= ks).



(* handling different paces among parties *)
op advSt ['l,'e] step (ss: (L,EnvL) APIst) (st: ('l,'e) APIst) : bool =
 exists n st', 0 <= n /\ equivSt ss st' /\ stepPiter step n st' = Some st.

lemma advSt0 ['l, 'e] step s1 (s2: ('l, 'e) APIst):
 equivSt s1 s2 => advSt step s1 s2.
proof.
move=> *; exists 0 s2; progress.
by rewrite stepPiter0.
qed.

lemma nosmt advSt_callSt ['l, 'e] step s1 (s2: ('l, 'e) APIst):
 advSt step s1 s2 =>
 callSt s1 <> None =>
 equivSt s1 s2.
proof.
move=> [k st'] /> *.
have ?: callSt st' <> None by smt().
move: (callSt_stepPiter step k st' H4); move=> [?|?].
 by move: H2; rewrite stepPiter0 //.
by move: H2; rewrite H5.
qed.



(* END languages *)




(* Global state for the multi-target setting (every party uses the same language) *)
type GlobalMTSt = { P1: StateL1
                  ; P2: StateL2
                  ; P3: StateL3
                  ; ibmt: sharedValue_t option
                  ; obmt: sharedValue_t option
                  }.




(* updates a local state after a [stepP] *)
op upd_P1 (newst: (L1,EnvL1) ECall) (st: GlobalMTSt): GlobalMTSt=
 {| st with P1 = st_from_step newst |}.
op upd_P2 (newst: (L2,EnvL2) ECall) (st: GlobalMTSt): GlobalMTSt=
 {| st with P2 = st_from_step newst |}.
op upd_P3 (newst: (L3,EnvL3) ECall) (st: GlobalMTSt): GlobalMTSt=
 {| st with P3 = st_from_step newst |}.
(* updates all local states after a [stepS] *)
op upd_P_API (r: apiRes_data option) (st: GlobalMTSt): GlobalMTSt =
 {| st with P1 = updRes r (P1 st); P2 = updRes r (P2 st); P3 = updRes r (P3 st) |}.
(* updates the input buffer *)
op upd_ibmt (newib: sharedValue_t option) (st: GlobalMTSt): GlobalMTSt =
 {| st with ibmt = newib |}.
(* updates the output buffer *)
op upd_obmt (newob: sharedValue_t option) (st: GlobalMTSt): GlobalMTSt =
 {| st with obmt = newob |}.


(* initial [GlobalMTSt] *)
op init_GlobalMTSt (P: L) : GlobalMTSt =
 {| P1 = iniSt (initStateL1 (compiler1 P))
  ; P2 = iniSt (initStateL2 (compiler2 P))
  ; P3 = iniSt (initStateL3 (compiler3 P))
  ; ibmt = None
  ; obmt = None
 |}.

module ProgSemMT (API: API_t) = {
  var st: GlobalMTSt
  proc init(P: L): unit = {
    API.api_init();
    st <- init_GlobalMTSt P;
  }
  (* Step Public *)
  proc stepP(id: partyId_t): bool = {
    var r <- false;
    var newst1 <- stepL1 (progSt (P1 st)) (envSt (P1 st)) (resSt (P1 st));
    var newst2 <- stepL2 (progSt (P2 st)) (envSt (P2 st)) (resSt (P2 st));
    var newst3 <- stepL3 (progSt (P3 st)) (envSt (P3 st)) (resSt (P3 st));
    if (id = 1 && callSt (P1 st) = None && newst1 <> None) {
      r <- true;
      st <- upd_P1 (oget newst1) st;
    }
    if (id = 2 && callSt (P2 st) = None && newst2 <> None) {
      r <- true;
      st <- upd_P2 (oget newst2) st;
    }
    if (id = 3 && callSt (P3 st) = None && newst3 <> None) {
      r <- true;
      st <- upd_P3 (oget newst3) st;
    }
    return r;
  }
  (* Step Secret *)
  proc stepS(): sideInfo_t option = {
    var x, v, t;
    var r <- None;
    var ecall <- syncPoint [callSt (P1 st); callSt (P2 st); callSt (P3 st)];
    if (ecall <> None) { (* call to the API *)
      match (oget ecall) with
      | Call_declass a => { (v, t) <@ API.api_declass(a);
                            r <- Some t;
                            (* updates API result *)
                            st <- upd_P_API (Some v) st;
                          }
      | Call_in a => { if (ibmt st <> None) {
                         t <@ API.api_in(a, oget (ibmt st));
                         r <- Some t;
                         st <- upd_ibmt None st; (* clears buffer *)
                         st <- upd_P_API None st; (* resets call *)
                       }
                     }
      | Call_out a => { if (obmt st = None) {
                          (x, t) <@ API.api_out(a);
                          r <- Some t;
                          st <- upd_obmt (Some x) st; (* fills buffer *)
                          st <- upd_P_API None st; (* resets call *)
                          }
                      }
      | Call_sop o a pargs sargs => { t <@ API.api_sop(o, pargs, sargs, a);
                                      r <- Some t;
                                      st <- upd_P_API None st; (* resets call *)
                                    }
      end;
    }
    return r;
  }
  proc setInput(x: sharedValue_t): bool = {
    var r <- false;
    if (ibmt st = None) {
      r <- true;
      st <- upd_ibmt (Some x) st;
    }
    return r;
  }
  proc getOutput(): sharedValue_t option = {
    var r: sharedValue_t option;
    r <- obmt st;
    if (r <> None) {
      st <- upd_obmt None st;
    }
    return r;
  }
}.



module RealSemMT: RealSemInterface = {
  module PSem = ProgSemMT(API_Real)
  include PSem
}.

module AdvOrclMT (Sem: AdvSemInterface) : AdvSemInterface = {
  (* Simulator runs a local copy of all parties... *)
  module SemEmu = RealSemMT
  include SemEmu [- init, stepP, stepS]

  proc init(P:L): unit = {
    SemEmu.init(P);
  }
  (* [stepP] relies on the local [RealSemMT] module in order to
     control the execution of each party.
     It leaves [Sem] untouched *)
  proc stepP = SemEmu.stepP
  (* Step Secret *)
  proc stepS(): sideInfo_t option = {
    var b, i, v;
    var r <- None;
    var ecall <- syncPoint [callSt (P1 SemEmu.PSem.st);
                            callSt (P2 SemEmu.PSem.st);
                            callSt (P3 SemEmu.PSem.st)];
    if (ecall <> None) { (* call to the API *)
      (* advance the source into a sync-point *)
      i <- 0;
      b <- true;
      while (b) {
        b <@  Sem.stepP(1);
        b <@  Sem.stepP(2);
        b <@  Sem.stepP(3);
        i <- i + 1;
      }
      (* do a [stepS] at the source *)
      r <@ Sem.stepS();
      if (r <> None) {
          match (oget ecall) with
          | Call_declass a => { v <- leakage_value (oget (oget r).`leakage);
                                (* updates API result *)
                                RealSemMT.PSem.st <- upd_P_API (Some (oget v)) RealSemMT.PSem.st;
                              }
          | Call_in a => { RealSemMT.PSem.st <- upd_P_API None RealSemMT.PSem.st; (* resets call *)
                         }
          | Call_out a => { RealSemMT.PSem.st <- upd_P_API None RealSemMT.PSem.st; (* resets call *)
                          }
      | Call_sop o a pargs sargs => { RealSemMT.PSem.st <- upd_P_API None RealSemMT.PSem.st; (* resets call *)
                                    }
      end;
      }        
    }
    return r;
  }
}.

module AdvMT (A: AdvInterface) (S:AdvSemInterface) : AdvEnvInterface = {
  module AdvO = AdvOrclMT(S)
  module Adv = A(AdvO)
  proc init(P: L): unit = {
    AdvO.init(P);
    Adv.init(P);
  }
  proc activate = Adv.activate
}.

module REAL_MT (E: Env) (A: AdvInterface) = {
  module Sem = RealSemMT
  module Adv = A(Sem)
  module Z = E(EnvO(Sem, Adv))
  proc game(P: L): bool = {
    var b;
    Sem.init(P);
    Adv.init(P);
    b <@ Z.animate();
    return b;
  }
}.


section MTSecurityProof.

declare module A: AdvInterface{ProgSem, ProgSemMT, AdvOrclMT}.
declare module Z: Env{A, API_Real, ProgSem, ProgSemMT, AdvOrclMT}.

op inv (stMT1 stMT2: GlobalMTSt) (stST2: GlobalSt) =
 stMT2.`P1 = stMT1.`P1 /\
 stMT2.`P2 = stMT1.`P2 /\
 stMT2.`P3 = stMT1.`P3 /\
 stST2.`ib = stMT1.`ibmt /\
 stST2.`ob = stMT1.`obmt /\
 stST2.`Sigma.[1] <> None /\
 stST2.`Sigma.[2] = stST2.`Sigma.[1] /\
 stST2.`Sigma.[3] = stST2.`Sigma.[1] /\
 advSt stepL1 (oget stST2.`Sigma.[1]) stMT1.`P1 /\
 advSt stepL2 (oget stST2.`Sigma.[1]) stMT1.`P2 /\
 advSt stepL3 (oget stST2.`Sigma.[1]) stMT1.`P3.

local lemma nosmt stepP_prop:
 equiv [ RealSemMT.stepP ~ AdvOrclMT(RealSem).stepP:
         ={id} /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
         ==>
         ={res} /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2} ].
proof.
proc; wp; skip; rewrite /inv; progress.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
- move: H7 => [??[?[??]]].
  exists (n+1) st'; progress; rewrite /upd_P1 /=; first smt().
  apply: (stepPiterS_some _ _ _ _ _ _ H15) => //=.
  by rewrite -some_oget //.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
  smt(). smt(). smt().
- move: H8 => [??[?[??]]].
  exists (n+1) st'; progress; rewrite /upd_P2 /=; first smt().
  apply: (stepPiterS_some _ _ _ _ _ _ H16) => //=.
  by rewrite -some_oget //.
- smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
  smt(). smt(). smt().
- move: H9 => [??[?[??]]].
  exists (n+1) st'; progress; rewrite /upd_P3 /=; first smt().
  apply: (stepPiterS_some _ _ _ _ _ _ H17) => //=.
  by rewrite -some_oget //.
- smt(). smt(). smt().
qed.

local lemma nosmt stepS_prop:
 equiv [ RealSemMT.stepS ~ AdvOrclMT(RealSem).stepS:
         true /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2}
         ==>
         ={res} /\ ={API_Real.senv} /\
         inv ProgSemMT.st{1} ProgSemMT.st{2} ProgSem.st{2} ].
proof.
proc.
sp 2 2; simplify.
if; [smt() | | by skip; progress].
seq 0 0: ((exists ks ss',
            stepPiter stepL ks (oget ProgSem.st{2}.`Sigma.[1])
            = Some ss' /\
            equivSt ss' ProgSemMT.st{1}.`P1 /\ 0 <= ks)
          /\ #[/:]pre).
 skip; rewrite /inv => |> *.
 move: H7 => [??[?[??]]].
 apply (bisim_backward1 _ _ _ _ H11 H12 _); smt(). 
elim* => ??.
exists* (oget ProgSem.st{2}.`Sigma.[1]); elim* => ss.
conseq (_: ss = oget ProgSem.st{2}.`Sigma.[1] /\
           stepPiter stepL ks ss = Some ss' /\
           equivSt ss' ProgSemMT.st{1}.`P1 /\
           equivSt ss' ProgSemMT.st{1}.`P2 /\
           equivSt ss' ProgSemMT.st{1}.`P3 /\
           ={r,ecall,API_Real.senv} /\
           0 <= ks /\ r{2}=None /\
           ecall{2} = callSt ProgSemMT.st{2}.`P1 /\
           ecall{2} = callSt ProgSemMT.st{2}.`P2 /\
           ecall{2} = callSt ProgSemMT.st{2}.`P3 /\
           ecall{2} <> None /\
           ProgSemMT.st{2}.`P1 = ProgSemMT.st{1}.`P1 /\
           ProgSemMT.st{2}.`P2 = ProgSemMT.st{1}.`P2 /\
           ProgSemMT.st{2}.`P3 = ProgSemMT.st{1}.`P3 /\
           ProgSem.st{2}.`ib = ProgSemMT.st{1}.`ibmt /\
           ProgSem.st{2}.`ob = ProgSemMT.st{1}.`obmt /\
           ProgSem.st{2}.`Sigma.[1] <> None /\
           ProgSem.st{2}.`Sigma.[2] = ProgSem.st{2}.`Sigma.[1] /\
           ProgSem.st{2}.`Sigma.[3] = ProgSem.st{2}.`Sigma.[1]
           ==> _).
 rewrite /inv => |> *; auto.
 split; [|split; [|smt()]].
  move: H11 => [??[?[??]]].
  move: (bisim_backward2 _ _ _ _ H14 H15 _); first smt().
  move=> [??] [?[??]].
  have ?:= (stepPiter_det _ _ _ _ _ _ _ _ H _ H16 _); first 4 smt().
  by move: H16; rewrite -H19 H; move => /#.
 move: H12 => [??[?[??]]].
 move: (bisim_backward3 _ _ _ _ H14 H15 _); first smt().
 move=> [??] [?[??]].
 have ?:= (stepPiter_det _ _ _ _ _ _ _ _ H _ H16 _); first 4 smt().
 by move: H16; rewrite -H19 H; move => /#.
seq 0 3: (ss' = (oget ProgSem.st{2}.`Sigma.[1]) /\
          #[/3:]pre).          
 sp 0 2.
 while {2} ((b = (i <= ks)){2} /\
             0 <= i{2} <= ks+1 /\ 
             (stepPiter stepL ks ss = Some ss') /\
             (stepPiter stepL (i+b2i b-1) ss = ProgSem.st{2}.`Sigma.[1]){2} /\
             #[/5:]pre
            ) (ks+1-i{2}).
   move=> *; exlim ProgSem.st => sw.
   case (i = ks).
    wp; call (stepP_spec 3 sw).
    call (stepP_spec 2 sw). 
    call (stepP_spec 1 sw).
    skip=> *.
    have Hloop: stepPiter stepL 1 (oget ProgSem.st{hr}.`Sigma.[1])
                = None.
     move: H; progress.
     move: H2; rewrite H18 b2i1 /= H1 => <- /=.
     by move: (callSt_stepPiter stepL 1 ss' _); smt().
    move: H; rewrite /inv;
    progress; 1..6,8..: smt(stepPiter0 get_set_id).
    - rewrite !H17 Hloop b2i0 /=; smt(get_setE).
   wp; call (stepP_spec 3 
    {| sw with Sigma = sw.`Sigma.[
        1 <- oget (stepPiter stepL 1 (oget (sw.`Sigma.[1])))].[
        2 <- oget (stepPiter stepL 1 (oget (sw.`Sigma.[1])))] |}).
   call (stepP_spec 2 {| sw with Sigma = sw.`Sigma.[
        1 <- oget (stepPiter stepL 1 (oget (sw.`Sigma.[1])))] |}). 
   call (stepP_spec 1 sw).
   skip => *.
   have Hloop: stepPiter stepL 1 (oget ProgSem.st{hr}.`Sigma.[1])
               <> None.
    apply (stepPiter_lt _ ks i{hr} ss); first 2 smt().
    rewrite -some_oget 1:/#.
    move: H; progress; smt().
   move: H; rewrite /inv; progress; 1..7,9..12: smt(get_setE).
   - rewrite !get_setE /=.
     rewrite H17 Hloop b2i1 /= -some_oget //.
     rewrite stepPiterS; first smt().
     move: H2; rewrite H18 b2i1 /= => ->.
     by rewrite (some_oget ProgSem.st{hr}.`Sigma.[1]) /#.
 skip; progress; 1..2,4..5: smt().
 by rewrite b2i1 /= stepPiter0 // -some_oget /#.
inline RealSem.stepS.
seq 0 2: (#[/:]pre /\ r0{2} = None /\ ecall{1}=ecall0{2}).
 wp; skip; rewrite /inv; progress.
 rewrite /allECalls (_:3 = 1+1+1) 1:// !iotaS // iota1 /=.
 by rewrite !H12 !H13 /= H3 (equivSt_callSt _ _ H) /#.
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
  inline API_Real.api_declass.
  rcondt {2} 7.
   move=> *; inline*; wp; rnd; wp; skip; progress; smt().
  inline*; sp.
  seq 1 1: (#pre /\ ={t0}); first by rnd; skip; progress; smt().
  sp; match {2}.
  + move=> *; wp; skip; progress; first 5 smt().
    - by rewrite /upd_SigmaAPI /= mapE /= /updRes /upd_ib /=
                 (some_oget st_R.`Sigma.[1]) // /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - exists 0 (upd_P_API (Some (oget (leakage_value (oget t0{2}.`leakage)))) st_L).`P1.
      split; first done.
      split; last by apply stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_SigmaAPI
                 /= mapE /= /updRes /= oget_omap_some /#.
    - exists 0 (upd_P_API (Some (oget (leakage_value (oget t0{2}.`leakage)))) st_L).`P2.
      split; first done.
      split; last by apply stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_SigmaAPI
                 /= mapE /= /updRes /= oget_omap_some /#.
    - exists 0 (upd_P_API (Some (oget (leakage_value (oget t0{2}.`leakage)))) st_L).`P3.
      split; first done.
      split; last by apply stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_SigmaAPI
                 /= mapE /= /updRes /= oget_omap_some /#.
  + move=> *; wp; skip; progress; smt().
  + move=> *; wp; skip; progress; smt().
  + move=> *; wp; skip; progress; smt().
- (* call_in *)
  if => //=; [smt() | |]; last first.
   rcondf {2} 2; first by move=>*; wp; skip; progress.
   by wp; skip; progress; smt(advSt0).
  seq 1 1: (#pre /\ ={t}).
   call (_: ={API_Real.senv} /\ a{1}=a0{2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
  rcondt {2} 5; first by move=>*; wp; skip; progress.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /= mapE /= /updRes /upd_ib /=
                 (some_oget st_R.`Sigma.[1]) // /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /upd_ib /= !mapE /= /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P1.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P2.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P3.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
- (* call_out *)
  if => //=; [smt() | |]; last first.
   rcondf {2} 2; first by move=>*; wp; skip; progress.
   by wp; skip; progress; smt(advSt0).
  seq 1 1: (#pre /\ ={x, t}).
   call (_: ={API_Real.senv} /\ a{1}=a0{2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt().
  rcondt {2} 5; first by move=>*; wp; skip; progress.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - by rewrite /upd_SigmaAPI /upd_P_API /upd_obmt /= mapE /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /upd_ob /= !mapE /= /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P1.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P2.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P3.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
  + wp; skip; progress; smt().
- (* call_sop *)
  seq 1 1: (#pre /\ ={t}).
   call (_: ={API_Real.senv} /\
            (o,pargs,sargs,a){1}=(o0,pargs0,sargs0,a0){2}).
    by inline*; wp; rnd; wp; skip; progress.
   by skip; progress; smt(advSt0).
  rcondt {2} 4; first by move=>*; wp; skip; progress.
  sp; match {2}; move=> *.
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; progress; smt().
  + wp; skip; rewrite /inv => |>*; progress; first 3 smt().
    - rewrite /upd_SigmaAPI /= mapE /= /updRes /upd_ib /=
              (some_oget st_R.`Sigma.[1]) // /#.
    - by rewrite /upd_SigmaAPI /= !mapE /= /#.
    - by rewrite /upd_SigmaAPI /= !mapE /= /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P1.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P2.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
    - exists 0 (upd_P_API None (upd_ibmt None st_L)).`P3.
      split; first done.
      split; last by rewrite stepPiter0.
      by rewrite /equivSt /upd_P_API /upd_ibmt /upd_SigmaAPI
                 /= mapE /= /upd_ib /= /updRes /= get_some /#.
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


end MultiThreaded.

(*
print MultiThreaded.SecurityMT.
*)
