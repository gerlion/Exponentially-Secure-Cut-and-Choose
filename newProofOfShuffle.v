Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
Require Import Coq.ZArith.ZArith.
From Groups Require Import groups module vectorspace.
Require Import Coq.Bool.Bool.
Require Import sigmaprotocol.
Require Import Field. 
Require Import Field_theory.
From CoLoR Require Import VecUtil VecArith Matrix NatUtil.
Require Import VectorUtil.
Require Import Coq.Logic.FinFun.
Require Import Lia.

Module BasicSigmas (Group : GroupSig)(Field : FieldSig)(VS : VectorSpaceSig Group Field).
Import Field.
Import VS.

Module BinGroup <: GroupSig.
 Definition G := bool.
 Definition Gdot := xorb.
 Definition Gone := false.
 Definition Gbool_eq := Bool.eqb.
 Definition Ginv (a : G) := a.

 Lemma module_abegrp : AbeGroup bool xorb false Bool.eqb id.
 Proof.
  constructor. constructor. constructor. intros. rewrite xorb_assoc. trivial.
  intros. apply xorb_false_l . intros. apply xorb_false_r. split; intros; 
  apply eqb_true_iff; auto. intros; split; apply eqb_false_iff; auto.
  intros. destruct x; simpl; auto. intros. destruct x; simpl; auto.
  apply xorb_comm.
 Qed.
End BinGroup.

Module Type Function.
     Parameter Pub : Set.
     Parameter Sec : Set.
     Parameter Out : Set.
     Parameter dec : Out -> Out -> bool.

     Parameter Fun : Pub -> Sec -> Out.
  End Function.

  Module Type SigmaOfFunction (Fun : Function).
    Import Fun.

    Definition Stat := prod Pub Out.
    Definition W := Sec.                          
    Definition Rel (s : Stat)(r : W):= dec (Fun s.1 r) s.2.
    Parameter C : Type.
    Parameter R : Type.
    Parameter T : Type.                              (* The set of responses  *)
    Parameter P0 : Stat -> R -> W -> (Stat*C).            (* The initial step of the prover, outputs a commit *)
    Parameter V0 : (Stat*C) -> bool -> (Stat*C*bool).           (* The initial step of the verifier, outputs a challenge *)
    Parameter P1 : (Stat*C*bool) -> R -> W -> (Stat*C*bool*T).  (* The final step of the prover, outputs a response *)
    Parameter V1 : (Stat*C*bool*T) -> bool.               (* The final step of the verifier *)
    Parameter simulator : Stat -> T -> bool -> (Stat*C*bool*T). (* The simulator *)
    Parameter simMap    : Stat -> W -> bool -> R -> T.    (* An explicit mapping between honest and simulated *)
    Parameter simMapInv : Stat -> W -> bool -> T -> R.    (* A function we use to show simMap is a bijection 
      between R and T when fixing the other variables *)
    Parameter extractor : T -> T -> bool -> bool -> W.   (* The extractor *)

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.
  
    Axiom SP : SigmaProtocol Form.

    Axiom V1FreeLeft : forall c1 c1' c0  c t,
      V1 (c0,c1,c,false,t) = V1 (c0,c1',c,false,t).    

   Axiom V1FreeRight : forall c0 c0' c1 c t,
      V1 (c0,c1,c,true,t) = V1 (c0',c1,c,true,t).    

    Axiom simFreeRightCom : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).1.1.2  = (simulator (c0',c1) t true).1.1.2.

    Axiom simFreeRightResp : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).2  = (simulator (c0',c1) t true).2.  

  Axiom simFreeLeftCom : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).1.1.2  = (simulator (c0,c1') t false).1.1.2.

    Axiom simFreeLeftResp : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).2  = (simulator (c0,c1') t false).2.      

    

  End SigmaOfFunction.

  Module Type Nat.
    Parameter N : nat.
  End Nat.

  Lemma simplV0 : forall E (Sig : Sigma.form E),
    SigmaProtocol Sig -> 
    (forall s r w e,
    (Sigma.P0 Sig s r w, e) = 
      Sigma.V0 Sig (Sigma.P0 Sig s r w) e).
  Proof.
    intros. rewrite pres_v0. rewrite <- comp_v0; trivial.
  Qed.

  Module ProofOfShuffle (N : Nat)(Fun : Function)
      (Sig : SigmaOfFunction Fun).
    Import Fun.    
    Import N.
    
    Definition Stat := prod (vector Pub N) (vector Out N).
    Definition W := prod (vector Sec N) (Permutation N).                        
    Definition Rel (s : Stat)(r : W):= 
      let '(c0, c1) := s in
      let '(r,  pi) := r in
      bVforall2 dec (Permute (Vbuild(fun i (ip : i < N) => 
      Fun (Vnth c0 ip) (Vnth r ip))) pi) c1.
    Definition C := vector Sig.C N.
    Definition R := prod (Permutation N) (vector Sig.R N).
    Definition T := prod (Permutation N) (vector Sig.T N).                   
    Definition P0 (s : Stat)(r : R)(w : W) : (Stat*C) :=
      (s,Permute
          (Vbuild (fun j (jp : j < N) => (Sig.P0 (Vnth (Permute s.1 w.2) jp,Vnth s.2 jp)
          (Vnth r.2 jp) (Vnth (Permute w.1 w.2) jp)).2))
        r.1).
    Definition V0 (s : Stat*C)(e : bool) :=
      (s,e).
    Definition P1 (s : Stat*C*bool)(r : R)(w : W) : 
          (Stat*C*bool*T) :=
      (s,(if s.2 then r.1 else (ComposePerm w.2 r.1),
          (Vbuild (fun j (jp : j < N) => (Sig.P1 
      (Vnth (Permute (Permute s.1.1.1 w.2) r.1) jp,
      Vnth (Permute s.1.1.2 r.1) jp,
          Vnth s.1.2 jp, s.2)
          (Vnth (Permute r.2 r.1) jp) 
           (Vnth (Permute (Permute w.1 w.2) r.1) jp)).2))
        )
      ).
    Definition V1 (s : Stat*C*bool*T) : bool :=
      let '(stat,com,chall,resp) := s in
      bVforall (fun a => a) (Vbuild (fun j (jp : j < N) => 
          Sig.V1 (Vnth (Permute stat.1 resp.1) jp, 
          Vnth (Permute stat.2 resp.1)jp,Vnth com jp,chall, 
            Vnth resp.2 jp))
        ).

    Definition simulator (s : Stat)(t : T)(e : bool)
      : (Stat*C*bool*T) :=
      (s,Vbuild (fun j (jp : j < N) => (Sig.simulator (Vnth (Permute s.1 t.1) jp,
         Vnth (Permute s.2 t.1) jp)(Vnth t.2 jp) e).1.1.2),e,(t.1,
      Vbuild (fun j (jp : j < N) => (Sig.simulator (Vnth (Permute s.1 t.1) jp,
         Vnth (Permute s.2 t.1) jp)(Vnth t.2 jp) e).2))).

    Definition simMap (s : Stat)(w : W)(e : bool)(r : R) : T :=
        (if e then r.1 else (ComposePerm w.2 r.1),
        Vbuild (fun j (jp : j < N) => Sig.simMap (Vnth (Permute (Permute s.1 w.2) r.1) jp, 
        Vnth (Permute s.2 r.1) jp) (Vnth (Permute (Permute w.1 w.2) r.1) jp) 
       e (Vnth (Permute r.2 r.1) jp))).

    Definition simMapInv (s : Stat)(w : W)(e :bool )(t : T) : R :=
      (if e then t.1 else (ComposePerm (InvPermutation w.2) t.1),
       Vbuild (fun j (jp : j < N) => Sig.simMapInv (Vnth (Permute s.1 w.2) jp, 
      Vnth s.2 jp) (Vnth (Permute w.1 w.2) jp)
          e (if e then (Vnth (Permute t.2 (InvPermutation t.1)) jp) else 
            (Vnth (Permute t.2 (InvPermutation (ComposePerm (InvPermutation w.2) t.1))) jp)))).

    Definition extractor (t1 t2 : T)(c1 c2 : bool) : W :=
      if c1 then 
      (Vbuild (fun j (jp : j < N) => Sig.extractor (Vnth (Permute t1.2 (InvPermutation t2.1)) jp) 
        (Vnth (Permute t2.2 (InvPermutation t2.1)) jp) c1 c2), ComposePerm t2.1    (InvPermutation t1.1)  
        ) 
      else
        (Vbuild (fun j (jp : j < N) => Sig.extractor (Vnth (Permute t1.2 (InvPermutation t1.1)) jp) 
        (Vnth (Permute t2.2 (InvPermutation t1.1)) jp) c1 c2), ComposePerm t1.1  (InvPermutation t2.1)  
        ).

    Definition Form : Sigma.form bool := 
    Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv eqb
    (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.
  
    Lemma SP : SigmaProtocol Form.
    Proof.
     (* Basic structure *)
     pose Sig.SP. constructor; intros; trivial. apply BinGroup.module_abegrp.
     simpl. apply injective_projections; simpl; trivial. apply Veq_nth.
     intros. do 2 rewrite Vbuild_nth. destruct s. apply comp_sim1.
     (* Correctness *)
     intros. simpl. apply bVforall_nth_intro. intros. do 10 rewrite Vbuild_nth. simpl. destruct s. 
     pose Sig.SP. simpl in H. unfold Rel in H. destruct s0. destruct w. 
      simpl. destruct c. simpl.
     (* Case 1 *) rewrite <- (Sig.V1FreeRight 
    (Vnth t (proj2_sig (Vnth (sval p).1 (proj2_sig (Vnth (sval r.1).1 ip)))))).
    rewrite <- pres_p0. pose (@simplV0 bool Sig.Form s). rewrite e.
    rewrite Vbuild_nth. rewrite <- pres_p0. rewrite e. rewrite <- pres_p1. simpl.
    do 3 rewrite Vbuild_nth. apply correctness. simpl. unfold Sig.Rel. simpl.
     apply (bVforall2_elim_nth (proj2_sig (Vnth (sval r.1).1 ip))) in H.
    do 2 rewrite Vbuild_nth in H. apply H. 
      (* Case 2 *) rewrite Vbuild_nth. simpl.
     rewrite <- (Sig.V1FreeLeft 
    (Vnth t0 (proj2_sig (Vnth (sval r.1).1 ip)))).
    do 4 rewrite Vbuild_nth. simpl. rewrite <- pres_p0.
    pose (@simplV0 bool Sig.Form s). rewrite e. rewrite <- pres_p1.
    apply correctness. simpl. unfold Sig.Rel. simpl.
     apply (bVforall2_elim_nth (proj2_sig (Vnth (sval r.1).1 ip))) in H.
    do 2 rewrite Vbuild_nth in H. apply H.
   
    (* Soundness *)
    + simpl. unfold Rel. unfold extractor. destruct s0. 
    simpl in H0, H1. assert (e1 = negb e2).
    apply negb_true_iff  in H. destruct (e1). 
    cbn in H. destruct (e2). discriminate.
    auto. rewrite <- H. auto.
     case_eq (e2); intros; rewrite H3 in H2; rewrite H3 in H1.
    (* case 1 *)
    ++ simpl in H2. rewrite H2. apply bVforall2_nth_intro. intros. do 6 rewrite Vbuild_nth.
    apply (bVforall_elim_nth (proj2_sig
           (Vnth (sval (InvPermutation t2.1)).1 ip))) in H0. 
    apply (bVforall_elim_nth (proj2_sig
           (Vnth (sval (InvPermutation t2.1)).1 ip))) in H1. 
    do 2 rewrite Vbuild_nth in H0. do 2 rewrite Vbuild_nth in H1.
    destruct s. simpl in special_soundness.
    unfold Sig.Rel in special_soundness. apply (special_soundness ((Vnth t
        (proj2_sig
           (Vnth (sval t1.1).1
              (proj2_sig (Vnth (sval (InvPermutation t2.1)).1 ip))))), Vnth (t0) ip)
    (Vnth c (proj2_sig (Vnth (sval (InvPermutation t2.1)).1 ip)))); auto.
    simpl in *. rewrite H2 in H0.
    +++  rewrite <- (Sig.V1FreeLeft (Vnth t0 ip)) in H0. trivial.
    rewrite InvCorrProj2. apply H0.
    +++ simpl in H1. rewrite InvCorrProj in H1.
    rewrite Vbuild_nth in H1.  rewrite InvCorrProj in H1.
    simpl in H1. rewrite <- (Sig.V1FreeRight (Vnth t ip)).
    rewrite InvCorrProj2. apply H1.
    (* case 2 *)
    ++ simpl in H2. rewrite H2. apply bVforall2_nth_intro. intros. do 6 rewrite Vbuild_nth.
    apply (bVforall_elim_nth (proj2_sig (Vnth (sval (InvPermutation t1.1)).1 ip))) in H0. 
    apply (bVforall_elim_nth (proj2_sig (Vnth (sval (InvPermutation t1.1)).1 ip))) in H1. 
    do 2 rewrite Vbuild_nth in H0. do 2 rewrite Vbuild_nth in H1.
    destruct s. simpl in special_soundness. do 2 rewrite InvCorrProj2.
    unfold Sig.Rel in special_soundness.  apply (special_soundness ((Vnth t
        (proj2_sig
           (Vnth (sval t2.1).1
              (proj2_sig (Vnth (sval (InvPermutation t1.1)).1 ip))))), Vnth (t0) ip)
    (Vnth c (proj2_sig (Vnth (sval (InvPermutation t1.1)).1 ip)))); auto.
    +++  rewrite H2 in H0. clear H1. rewrite <- (Sig.V1FreeRight (Vnth t
     (proj2_sig
        (Vnth (sval t2.1).1
           (proj2_sig (Vnth (sval (InvPermutation t1.1)).1 ip)))))) in H0.
    rewrite Vbuild_nth in H0. rewrite InvCorrProj in H0.
   simpl in H0. apply H0.
    +++ rewrite Vbuild_nth in H1.
    rewrite <- (Sig.V1FreeLeft (Vnth t0 ip)) in H1.  apply H1.
    
    (* Zero-knowlege *)
    + split. intros. simpl in *. unfold P1, V0, P0, simulator, simMap. apply injective_projections.
    apply injective_projections. apply injective_projections. simpl. trivial. simpl. 
    (* Commitment *)
    ++ apply Veq_nth. intros. do 14 rewrite Vbuild_nth. destruct s.
    apply (bVforall_elim_nth ip) in H. simpl in H. do 14 rewrite Vbuild_nth in H. 
    (* Commit 1 *)
    destruct (e). +++ simpl in H. rewrite <- (Sig.V1FreeRight (Vnth s0.1
      (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))) in H. simpl in H.
   rewrite <- pres_p0 in H. pose Sig.SP.  rewrite (@simplV0 bool Sig.Form s) in H.
    rewrite <- pres_p1 in H. destruct (honest_verifier_ZK (Vnth s0.1
      (proj2_sig
         (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))),
   Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))
   (Vnth w.1
      (proj2_sig
         (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))
   true (Vnth r.2 (proj2_sig (Vnth (sval r.1).1 ip))) (Vnth t.2 ip)). 
    apply H0 in H. rewrite <- (Sig.simFreeRightCom (Vnth s0.1
      (proj2_sig
         (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))).
    simpl. symmetry in H. simpl in H. rewrite H. symmetry. simpl in *.
    rewrite pres_p1. rewrite pres_v0. simpl. trivial.
    (* Commit 2 *)
    +++  simpl in H. rewrite Vbuild_nth in H.
   rewrite <- (Sig.V1FreeLeft (Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))) in H. 
    rewrite <- pres_p0 in H. pose Sig.SP.  rewrite (@simplV0 bool Sig.Form s) in H.
    rewrite <- pres_p1 in H. destruct (honest_verifier_ZK (Vnth s0.1
      (proj2_sig
         (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))),
   Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))
   (Vnth w.1
         (proj2_sig
            (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))
   false (Vnth r.2 (proj2_sig (Vnth (sval r.1).1 ip))) (Vnth t.2 ip)). 
   simpl in *. apply H0 in H. rewrite <- (Sig.simFreeLeftCom (Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))).
   simpl. symmetry in H. simpl in H. rewrite Vbuild_nth.  clear H0. clear H1. rewrite H. symmetry. simpl in *. rewrite pres_p1. rewrite pres_v0. simpl. trivial.
    (* Challenge *)
    ++ simpl. trivial.
    (* Response *)
    ++ simpl. destruct (e); apply injective_projections. simpl. trivial.
    (* Challenge 1 *)
   +++ simpl in H. simpl. apply Veq_nth. intros. do 14 rewrite Vbuild_nth.
    apply (bVforall_elim_nth ip) in H. simpl in H. do 13 rewrite Vbuild_nth in H. 
    rewrite <- (Sig.V1FreeRight (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip))))))
    in H. simpl in *. destruct s. rewrite <- pres_p0 in H. pose Sig.SP.  rewrite (@simplV0 bool Sig.Form s) in H.
    rewrite <- pres_p1 in H. destruct (honest_verifier_ZK (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))),
   Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))
   (Vnth w.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))
   true (Vnth r.2 (proj2_sig (Vnth (sval r.1).1 ip))) (Vnth t.2 ip)). 
    apply H0 in H. rewrite <- (Sig.simFreeRightResp (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))).
   simpl. symmetry in H. simpl in H. rewrite H. symmetry. simpl in *.
   rewrite <- pres_p0. rewrite (@simplV0 bool Sig.Form s). trivial.
    (* Challenge 2 *)
    +++  simpl. trivial.
    +++ simpl in H. simpl. apply Veq_nth. intros. do 14 rewrite Vbuild_nth.
    apply (bVforall_elim_nth ip) in H. simpl in H. do 14 rewrite Vbuild_nth in H. 
    rewrite <- (Sig.V1FreeLeft (Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip))))
    in H. simpl in *. destruct s. rewrite <- pres_p0 in H.   pose Sig.SP.  
    rewrite (@simplV0 bool Sig.Form s) in H.
    rewrite <- pres_p1 in H. destruct (honest_verifier_ZK (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))),
   Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))
   (Vnth w.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval r.1).1 ip)))))
   false (Vnth r.2 (proj2_sig (Vnth (sval r.1).1 ip))) (Vnth t.2 ip)). 
   simpl in *. clear H1. do 2 rewrite Vbuild_nth in H.
    apply H0 in H. rewrite <- (Sig.simFreeLeftResp (Vnth s0.2 (proj2_sig (Vnth (sval r.1).1 ip)))).
   simpl. symmetry in H. simpl in H. rewrite Vbuild_nth. rewrite H. simpl in *.
   rewrite <- pres_p0. rewrite (@simplV0 bool Sig.Form s). trivial.

    (* Bijective *)
    ++ destruct s. split.
    +++ simpl. unfold simMapInv, simMap. destruct e.  apply injective_projections.
    simpl. trivial. simpl. apply Veq_nth. intros. do 11  rewrite Vbuild_nth. simpl.
    ++++ do 3 rewrite InvCorrProj.
  destruct (honest_verifier_ZK (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 ip)), Vnth s0.2 ip)
     (Vnth w.1 (proj2_sig (Vnth (sval w.2).1 ip))) true
     (Vnth r.2 ip) (Vnth t.2 ip)). destruct H0. simpl in *. 
     rewrite H0. trivial. 
    ++++ apply injective_projections. simpl. rewrite ComposePermAss.
    rewrite CompPermutationInv. rewrite CompPermutationId. trivial.
    do 2 rewrite Prod_right_replace. apply Veq_nth. intros. do 10 rewrite Vbuild_nth. simpl.
     rewrite InvCorrProj3. destruct r.1. destruct (a i ip). rewrite H.
    do 3 rewrite Vbuild_nth. rewrite H. destruct (honest_verifier_ZK 
    (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 ip)), Vnth s0.2 ip)
     (Vnth w.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (MakeIndex ip))))) false
     (Vnth r.2 ip) (Vnth t.2 ip)). destruct H2. simpl in *. 
    rewrite H2. trivial.
    (* Other direction *) 
    +++ simpl. unfold simMapInv, simMap. destruct e.  apply injective_projections.
    simpl. trivial. simpl. apply Veq_nth. intros. do 11  rewrite Vbuild_nth.
    ++++ rewrite InvCorrProj2.
  destruct (honest_verifier_ZK (Vnth s0.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval t.1).1 ip)))),
  Vnth s0.2 (proj2_sig (Vnth (sval t.1).1 ip)))
     (Vnth w.1 (proj2_sig (Vnth (sval w.2).1 (proj2_sig (Vnth (sval t.1).1 ip))))) true
     (Vnth r.2 ip) (Vnth t.2 ip)). destruct H0. simpl in *. 
     rewrite H1. trivial. 
    ++++ apply injective_projections. rewrite ComposePermAss.
    rewrite CompPermutationInv2. rewrite CompPermutationId. trivial.
    apply Veq_nth. intros. do 1 rewrite Vbuild_nth. do 2 rewrite ComposePermCorrect.
    rewrite ComposePermAss. rewrite CompPermutationInv2. rewrite CompPermutationId.
    do 10 rewrite Vbuild_nth. simpl. rewrite InvCorrComp.
    assert (Vnth t.2 (proj2_sig (Vnth (PermuteInv (sval t.1).2 
      (InvPermutation w.2)) (proj2_sig (Vnth (sval (InvPermutation w.2)).1 
      (proj2_sig (Vnth (sval t.1).1 ip)))))) = Vnth t.2 ip).
    destruct t.1, w.2. simpl. rewrite Vbuild_nth. simpl.
    destruct (a0 (sval (Vnth x.1 ip)) (proj2_sig (Vnth x.1 ip))).
    rewrite H. simpl. destruct (a i ip). rewrite H2. simpl. trivial.
    rewrite H. destruct (honest_verifier_ZK (Vnth s0.1 (proj2_sig (Vnth (sval t.1).1 ip)),
  Vnth s0.2 (proj2_sig (Vnth (sval (InvPermutation w.2)).1 (proj2_sig (Vnth (sval t.1).1 ip)))))
     (Vnth w.1 (proj2_sig (Vnth (sval t.1).1 ip))) false
     (Vnth r.2 ip) (Vnth t.2 ip)). destruct H1. simpl in *. 
    rewrite H2. trivial. 

    (* Simulator Correct *)
    + simpl. apply bVforall_nth_intro. intros. do 3 rewrite Vbuild_nth.
    destruct s. rewrite pres_sim. remember ((Sigma.simulator Sig.Form (Vnth (Permute s0.1 t.1) ip, Vnth (Permute s0.2 t.1) ip)
      (Vnth t.2 ip) e).1.1) as a. 
 rewrite (chal_sim (Vnth (Permute s0.1 t.1) ip, Vnth (Permute s0.2 t.1) ip)
    (Vnth t.2 ip) e). rewrite Heqa. assert (forall A B (a:A*B), (a.1, a.2) = a). intros. apply injective_projections;
    simpl; trivial. rewrite H. rewrite <- chal_sim. rewrite H. apply simulator_correct.
    Qed.
    
  End ProofOfShuffle.

  Module Type ElGamalReEncryption <: Function.

     Parameter pk : prod G G.

     Definition Pub := prod G G. 
     Definition Sec := F.
     Definition Out := prod G G.
     Definition dec c c' := Gbool_eq c.1 c'.1 && Gbool_eq c.2 c'.2.

     Definition Fun c r := (c.1 o pk.1^r, c.2 o pk.2^r).
  End ElGamalReEncryption.


  Module ElGamalReEncryptionSigma (EG : ElGamalReEncryption) <: SigmaOfFunction EG.
    Import EG.

    Definition Stat := prod Pub Pub.
    Definition W := Sec. 

  (* Before publishing it would be nice to turn this into a module *)
  Definition Rel (stat : Stat)(w : W) := 
    dec (Fun stat.1 w) stat.2.
  Definition C := prod G G.
  Definition R := F.
  Definition T := F.                              (* The set of responses  *)

 (** Begin Sigma Proper *)
  Definition P0 (stat : Stat)(r : R)(w : W) : 
      (Stat*C) :=
    let '(c0, c1) := stat in     
    (stat,Fun c0 r).

  Definition V0 (ggtoxgtor: Stat*C) (c: bool):
     (Stat*C*bool)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: Stat*C*bool) 
      (r x: F) : Stat*C*bool*T :=
        let '((c0,c1),(a0,a1),c) := ggtoxgtorc in   
      (ggtoxgtorc, if c then r - x else r).

  Definition V1 (ggtoxgtorcs : Stat*C*bool*T) :=
    let '((c0,c1),a,c,t) := ggtoxgtorcs in   
    if c then dec a (Fun c1 t) else
      dec a (Fun c0 t).

  Definition simMap (s : Stat)(x : W)(c : bool)(r : T):=
    if c then r-x else r.

  Definition simMapInv (s : Stat)(x : W)(c : bool)(t :T):=
    if c then t+x else t.

  Definition simulator (stat :Stat)(t: T)(e : bool) :=
        let '(c0,c1) := stat in 
    if e then (stat,Fun c1 t,e,t) else 
    (stat,Fun c0 t,e,t).

  Definition extractor (s1 s2: T)(e1 e2 : bool) :=
    if e2 then s1-s2 else s2-s1.

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.

  Theorem SP
    :  SigmaProtocol Form. 
  Proof.
    pose module_abegrp. pose vs_field.
    constructor; intros; auto. apply BinGroup.module_abegrp.
    destruct s. auto.
    destruct sce, p, s, c. simpl. auto.
    simpl. unfold simulator. destruct s.
    destruct e; auto.  simpl. unfold simulator. 
    destruct s. destruct e; auto.
    simpl. unfold simulator. destruct s2.
    destruct s1. destruct e; auto.
    (* Correctness *)
    simpl. unfold V1, V0, P0. simpl in H.
    unfold rel in H. destruct s. apply andb_true_iff in H.
    destruct H. destruct c. apply andb_true_iff. split;
    apply bool_eq_corr; simpl; trivial.
    apply bool_eq_corr in H. apply bool_eq_corr in H0.
    unfold Fun in *. simpl in *. rewrite <- H. 
    rewrite <- dot_assoc.
    apply left_cancel. rewrite <- mod_dist_Fadd. apply f_equal. destruct f, F_R.
    rewrite Radd_assoc. rewrite (Radd_comm w r). rewrite <- Radd_assoc.
    rewrite Ropp_def. rewrite Radd_comm. rewrite Radd_0_l. trivial.
    apply bool_eq_corr in H. apply bool_eq_corr in H0. 
    simpl in *. rewrite <- H0. rewrite <- dot_assoc.
    apply left_cancel. rewrite <- mod_dist_Fadd. apply f_equal.
    destruct f, F_R. rewrite (Radd_comm r). rewrite Radd_assoc.
    rewrite Ropp_def. rewrite Radd_0_l. trivial.
     apply andb_true_iff. split;
    apply bool_eq_corr; simpl; trivial.
    (* Soundness *)
    simpl in *. destruct s, c. unfold BinGroup.Gbool_eq in H.
    apply negb_true_iff in H. destruct f, F_R. assert (e1 = negb e2). 
    destruct e1. destruct e2. simpl in H. discriminate. auto. rewrite <- H. auto.
    unfold rel, extractor. destruct e2. 
    (* Case 1 *)
    simpl in H2. rewrite H2 in H0.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    apply bool_eq_corr in H3. apply bool_eq_corr in H4.
    apply andb_true_iff. split; apply bool_eq_corr. simpl in *.
    rewrite mod_dist_Fadd. rewrite dot_assoc. rewrite <- H0. rewrite H1.
    rewrite <- dot_assoc. rewrite <- mod_dist_Fadd. rewrite Ropp_def. rewrite mod_ann.
    rewrite one_right. trivial. simpl in *. rewrite mod_dist_Fadd. rewrite dot_assoc.
    rewrite <- H3. rewrite H4.
    rewrite <- dot_assoc. rewrite <- mod_dist_Fadd. rewrite Ropp_def. rewrite mod_ann.
    rewrite one_right. trivial.
    (* Case 2 *)
    simpl in H2. rewrite H2 in H0.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    apply bool_eq_corr in H3. apply bool_eq_corr in H4.
    apply andb_true_iff. split; apply bool_eq_corr. simpl in *.
    rewrite mod_dist_Fadd. rewrite dot_assoc. rewrite <- H1. rewrite H0.
    rewrite <- dot_assoc. rewrite <- mod_dist_Fadd. rewrite Ropp_def. rewrite mod_ann.
    rewrite one_right. trivial. simpl in *. rewrite mod_dist_Fadd. rewrite dot_assoc. 
    rewrite <- H4. rewrite H3. rewrite <- dot_assoc. rewrite <- mod_dist_Fadd. 
    rewrite Ropp_def. rewrite mod_ann. rewrite one_right. trivial.
    (* Zero knowledge *)
    split. intros. simpl in *. unfold V1, P0, V0,
    simulator, simMap in *.
    destruct s, e. trivial. apply andb_true_iff in H.
    destruct H. apply bool_eq_corr in H. apply bool_eq_corr in H0.
    unfold Fun. simpl in *. rewrite H. rewrite H0. trivial. trivial.
    split; simpl; unfold simMapInv, simMap;
    destruct e; trivial; simpl in *. unfold R, T, Sec in *. ring; auto.
    unfold R, T, Sec in *. ring; auto.
    (* Simualtor corres *)
    simpl. unfold V1, simulator. destruct s, e;
    apply andb_true_iff; split; apply bool_eq_corr; auto.
  Qed.    

  Lemma V1FreeLeft : forall c1 c1' c0  c t,
      V1 (c0,c1,c,false,t) = V1 (c0,c1',c,false,t).  
  Proof.
    intros. simpl. trivial.
  Qed.   

  Lemma V1FreeRight : forall c0 c0' c1 c t,
      V1 (c0,c1,c,true,t) = V1 (c0',c1,c,true,t).   
  Proof.
    intros. simpl. trivial.
  Qed. 

  Lemma simFreeRightCom : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).1.1.2  = (simulator (c0',c1) t true).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeRightResp : forall c0 c0' c1 t,
      (simulator (c0,c1) t false).2  = (simulator (c0',c1) t false).2.
  Proof.
    intros. simpl. trivial.
  Qed.  

  Lemma simFreeLeftCom : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).1.1.2  = (simulator (c0,c1') t false).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeLeftResp : forall c1 c1' c0 t,
      (simulator (c0,c1) t true).2  = (simulator (c0,c1') t true).2. 
  Proof.
    intros. simpl. trivial.
  Qed.

  End ElGamalReEncryptionSigma.

  Module ARL := RingAddationalLemmas Field.
  Module AVL := VectorSpaceAddationalLemmas Group Field VS.

  Module Type ElGamalDecryption <: Function.

     Parameter PK : prod G G.
 
     Definition Pub := prod G G. 
     Definition Sec := {x : F | x <> 0}.
     (* We adopt the slightly odd notation of calling the output of the decryption,
      a message and a public key *)
     Definition Out := prod G G.
     Definition dec c c' := Gbool_eq c.1 c'.1 && Gbool_eq c.2 c'.2.

     Definition Fun (c : Pub)(r : Sec) := (c.1^(sval r),PK.1^(sval r)).
  End ElGamalDecryption.

  Definition div (a b : {x : F | x <> 0}) : {x : F | x <> 0}.
     Proof.
      pose vs_field.  intros. destruct a, b. exists (x/x0).
      unfold not. intros. apply AVL.F_mul_zero in H. destruct H.
      contradiction. apply n0. destruct f, F_R. assert (FmulInv x0 * x0 = 1).
      apply Finv_l. trivial. rewrite H in H0. ring_simplify in H0.
      symmetry in H0. contradiction. 
     Defined. 

  Definition mul (a b : {x : F | x <> 0}) : {x : F | x <> 0}.
     Proof.
      pose vs_field.  intros. destruct a, b. exists (x*x0).
      unfold not. intros. apply n0. apply (ARL.Fmul_left_cancel (FmulInv x)) in H.
      ring_simplify in H. destruct f. rewrite (Finv_l x n) in H. rewrite <- H.
      field; auto.
     Defined.

  Lemma eq_proj:
  forall a b : {x : F | x <> 0},
  a = b <-> proj1_sig(a) = proj1_sig(b). 
  Proof.
    split; intros.
    + rewrite H. auto.
    + destruct a, b. cbn in *.
      subst. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat; auto.
  Qed.

  Module ElGamalSigmaDec (EG : ElGamalDecryption) <: SigmaOfFunction EG.
    Import EG.

    Definition Stat := prod Pub Out.
    Definition W := Sec. 

  (* Before publishing it would be nice to turn this into a module *)
  Definition Rel (stat : Stat)(w : W)  : bool := 
    dec (Fun stat.1 w) stat.2.
  Definition C := Pub.
  Definition R := Sec.
  Definition T := Sec.                              (* The set of responses  *)

 (** Begin Sigma Proper *)
  Definition P0 (stat : Stat)(r : R)(w : W) : 
      (Stat*C) :=
    let '(c0, c1) := stat in     
    (stat,(c0.1^(sval r),PK.1^(sval r))).

  Definition V0 (ggtoxgtor: Stat*C) (c: bool):
     (Stat*C*bool)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: Stat*C*bool) 
      (r : R)(x : W) : Stat*C*bool*T :=
        let '((c0,c1),(a0,a1),c) := ggtoxgtorc in   
      (ggtoxgtorc, if c then div r x else r).

  Definition V1 (ggtoxgtorcs : Stat*C*bool*T) :=
    let '((c0,c1),a,c,t) := ggtoxgtorcs in   
    if c then dec a (c1.1^(sval t), c1.2^(sval t)) else
       dec a (c0.1^(sval t),PK.1^(sval t)).

  Definition simMap (s : Stat)(x : W)(c : bool)(r : T):=
    if c then div r x else r.

  Definition simMapInv (s : Stat)(x : W)(c : bool)(t :T):=
    if c then mul t x else t.

  Definition simulator (stat :Stat)(t: T)(e : bool) :=
        let '(c0,c1) := stat in 
    if e then (stat,((c1.1^(sval t)), c1.2^(sval t)),e,t) else 
    (stat,(c0.1^(sval t),PK.1^(sval t)),e,t).

  Definition extractor (s1 s2: T)(e1 e2 : bool) :=
    if e2 then div s1 s2 else div s2 s1.

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.

  Module ADL := ModuleAddationalLemmas Group Field VS.

  Theorem SP
    :  SigmaProtocol Form. 
  Proof.
    pose module_abegrp. pose vs_field. 
    constructor; intros; auto. apply BinGroup.module_abegrp.
    destruct s. auto.
    destruct sce, p, s, c. simpl. auto.
    simpl. unfold simulator. destruct s.
    destruct e; auto.  simpl. unfold simulator. 
    destruct s. destruct e; auto.
    simpl. unfold simulator. destruct s2.
    destruct s1. destruct e; auto.
    (* Correctness *)
    simpl. unfold V1, V0, P0. simpl in H.
    unfold rel in H. destruct s. apply andb_true_iff in H.
    destruct H. apply bool_eq_corr in H. apply bool_eq_corr in H0. destruct w, r. 
    destruct c. apply andb_true_iff. split; apply bool_eq_corr; simpl; trivial.
    unfold Sigma.W, Sigma.R in *. simpl in *.
    unfold W, R, Sec in *. rewrite <- H. unfold Fun in *. rewrite <- mod_dist_Fmul. 
    apply f_equal. simpl. field; auto. simpl in *. rewrite <- H0. rewrite <- mod_dist_Fmul.
    simpl. apply f_equal. field; auto. apply andb_true_iff;
    split; apply bool_eq_corr; simpl; trivial.
    (* Soundness *)
    simpl in *. destruct s, c. unfold BinGroup.Gbool_eq in H.
    apply negb_true_iff in H. destruct f, F_R. assert (e1 = negb e2). 
    destruct e1. destruct e2. simpl in H. discriminate. auto. rewrite <- H. auto.
    unfold rel, extractor. destruct t1, t2. destruct e2. 
    (* Case 1 *)
    simpl in H2. rewrite H2 in H0.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    apply bool_eq_corr in H3. apply bool_eq_corr in H4.
    apply andb_true_iff. split; apply bool_eq_corr. 
    simpl in *. unfold Fun in *. unfold div. simpl. rewrite ADL.mod_dist_FMul2. rewrite <- H0. rewrite H1.
    rewrite <- ADL.mod_dist_FMul2. replace (x0/x0) with 1. rewrite mod_id. trivial.
    field; auto. simpl. rewrite ADL.mod_dist_FMul2. simpl in *. rewrite <- H3. rewrite H4.
    rewrite <- ADL.mod_dist_FMul2. replace (x0/x0) with 1. rewrite mod_id. trivial.
    field; auto.
    (* Case 2 *)
    simpl in H2. rewrite H2 in H0.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    apply bool_eq_corr in H3. apply bool_eq_corr in H4.
    apply andb_true_iff. split; apply bool_eq_corr. unfold Fun in *. simpl in *.
     rewrite ADL.mod_dist_FMul2. rewrite <- H1. rewrite H0.
    rewrite <- ADL.mod_dist_FMul2. replace (x/x) with 1. rewrite mod_id. trivial.
    field; auto. simpl. rewrite ADL.mod_dist_FMul2. simpl in *. rewrite <- H4. rewrite H3.
    rewrite <- ADL.mod_dist_FMul2. replace (x/x) with 1. rewrite mod_id. trivial.
    field; auto.
    (* Zero knowledge *)
    split. intros. simpl in *. unfold V1, P0, V0,
    simulator, simMap in *.
    destruct s, e. trivial. apply andb_true_iff in H.
    destruct H. apply bool_eq_corr in H. apply bool_eq_corr in H0.
    unfold Fun. simpl in *. rewrite H. rewrite H0. trivial. trivial.
    split; simpl; unfold simMapInv, simMap;
    destruct e; trivial; simpl in *. unfold R, T, Sec in *. destruct r, w.
    apply eq_proj. simpl. field; auto. unfold R, T, Sec in *. destruct r, w.
    apply eq_proj. destruct t. simpl. field; auto.
    (* Simualtor corres *)
    simpl. unfold V1, simulator. destruct s, e;
    apply andb_true_iff; split; apply bool_eq_corr; simpl; auto.
  Qed.    

  Lemma V1FreeLeft : forall c1 c1' c0  c t,
      V1 (c0,c1,c,false,t) = V1 (c0,c1',c,false,t).  
  Proof.
    intros. simpl. trivial.
  Qed.   

  Lemma V1FreeRight : forall c0 c0' c1 c t,
      V1 (c0,c1,c,true,t) = V1 (c0',c1,c,true,t).   
  Proof.
    intros. simpl. trivial.
  Qed. 

  Lemma simFreeRightCom : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).1.1.2  = (simulator (c0',c1) t true).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeRightResp : forall c0 c0' c1 t,
      (simulator (c0,c1) t false).2  = (simulator (c0',c1) t false).2.
  Proof.
    intros. simpl. trivial.
  Qed.  

  Lemma simFreeLeftCom : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).1.1.2  = (simulator (c0,c1') t false).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeLeftResp : forall c1 c1' c0 t,
      (simulator (c0,c1) t true).2  = (simulator (c0,c1') t true).2. 
  Proof.
    intros. simpl. trivial.
  Qed.

  End ElGamalSigmaDec.


  (************************************************)
  (*                                              *)
  (*    Now we have the final one                 *)
  (*                                              *)
  (************************************************)

  Module Type ElGamalDeRe <: Function.

     Parameter PK : prod G G.

     Definition Pub := prod G G. 
     Definition Sec := prod F {x : F | x <> 0}.
                            (* Output ciphertext and the key it was decrypted with respect to *)
     Definition Out := prod (prod G G) G.
     Definition dec c c' := Gbool_eq c.1.1 c'.1.1 && Gbool_eq c.1.2 c'.1.2 && Gbool_eq c.2 c'.2.

     Definition Fun c (r : Sec) := ((c.1 o PK.1^r.1)^(sval r.2), 
          c.2 o PK.2^r.1, PK.1^(sval r.2)).
  End ElGamalDeRe.

  Module ElGamalSigmaKeyShift (EG : ElGamalDeRe) <: SigmaOfFunction EG.
    Import EG.

    Definition Stat := prod Pub Out.
    Definition W := Sec. 

  (* Before publishing it would be nice to turn this into a module *)
  Definition Rel (stat : Stat)(w : W)  : bool := 
    dec (Fun stat.1 w) stat.2.
  Definition C := Out.
  Definition R := Sec.
  Definition T := Sec.                              (* The set of responses  *)

 (** Begin Sigma Proper *)
  Definition P0 (stat : Stat)(r : R)(w : W) : 
      (Stat*C) :=
    let '(c0, c1) := stat in     
    (stat,((c0.1 o PK.1^r.1)^(sval r.2),
        c0.2 o PK.2^r.1,PK.1^(sval r.2))).

  Definition V0 (ggtoxgtor: Stat*C) (c: bool):
     (Stat*C*bool)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: Stat*C*bool) 
      (r : R)(x : W) : Stat*C*bool*T :=
        let '((c0,c1),(a0,a1),c) := ggtoxgtorc in   
      (ggtoxgtorc, if c then (r.1 - x.1,div r.2 x.2) else r).

  Definition V1 (ggtoxgtorcs : Stat*C*bool*T) :=
    let '((c0,c1),a,c,t) := ggtoxgtorcs in   
    if c then dec a (c1.1.1^(sval t.2) o a.2^t.1,c1.1.2 o PK.2^t.1,c1.2^(sval t.2)) else
       dec a ((c0.1 o PK.1^t.1)^(sval t.2),c0.2 o PK.2^t.1,PK.1^(sval t.2)).

  Definition simMap (s : Stat)(x : W)(c : bool)(r : T):=
    if c then (r.1 - x.1,div r.2 x.2) else r.

  Definition simMapInv (s : Stat)(x : W)(c : bool)(t :T):=
    if c then (t.1 + x.1, mul t.2 x.2) else t.

  Definition simulator (stat :Stat)(t: T)(e : bool) :=
        let '(c0,c1) := stat in 
    if e then (stat,(c1.1.1^(sval t.2) o (c1.2^(sval t.2))^t.1,c1.1.2 o PK.2^t.1,c1.2^(sval t.2)),e,t) else 
    (stat,((c0.1 o PK.1^t.1)^(sval t.2),c0.2 o PK.2^t.1,PK.1^(sval t.2)),e,t).

  Definition extractor (s1 s2: T)(e1 e2 : bool) :=
    if e2 then (s1.1-s2.1,div s1.2 s2.2) else (s2.1-s1.1,div s2.2 s1.2).

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.

  Module ADL := ModuleAddationalLemmas Group Field VS.

  Theorem SP
    :  SigmaProtocol Form. 
  Proof.
    pose module_abegrp. pose vs_field. 
    constructor; intros; auto. apply BinGroup.module_abegrp.
    destruct s. auto.
    destruct sce, p, s, c. simpl. auto.
    simpl. unfold simulator. destruct s.
    destruct e; auto.  simpl. unfold simulator. 
    destruct s. destruct e; auto.
    simpl. unfold simulator. destruct s2.
    destruct s1. destruct e; auto.
    (* Correctness *)
    simpl. unfold V1, V0, P0. simpl in H.
    unfold rel in H. destruct s. apply andb_true_iff in H. destruct H. apply andb_true_iff in H. 
    destruct H. apply bool_eq_corr in H. apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    destruct w, r. destruct c. apply andb_true_iff. split. apply andb_true_iff. split; apply bool_eq_corr.
    (* Number 1 *)
    simpl; trivial. unfold Sigma.W, Sigma.R in *. simpl in *. unfold W, R, Sec in *. rewrite <- H. 
    rewrite <- mod_dist_Fmul. simpl. assert (sval (div s0 s) * sval s = sval s0). destruct s, s0.
    simpl. field; auto. do 2 rewrite mod_dist_Gdot. do 2 rewrite <- mod_dist_Fmul.
    rewrite H2. rewrite <- dot_assoc. apply left_cancel. rewrite <- mod_dist_Fmul.
    rewrite <- mod_dist_Fadd. apply f_equal. field; auto.
    (* Number 2 *)
    simpl in *.  rewrite <- H1. rewrite <- dot_assoc. apply left_cancel. rewrite <- mod_dist_Fadd.
    apply f_equal. field; auto.
    (* Number 3 *)
    simpl in *. apply bool_eq_corr. rewrite <- H0. rewrite <- mod_dist_Fmul. apply f_equal.
    destruct s0, s. simpl. field; auto. auto.
    (* Finishing *)
    apply andb_true_iff; split. apply andb_true_iff; split. apply bool_eq_corr; simpl; trivial.
    apply bool_eq_corr; simpl; trivial. apply bool_eq_corr; simpl; trivial.
    (* Soundness *)
    simpl in *. destruct s, c. unfold BinGroup.Gbool_eq in H.
    apply negb_true_iff in H. destruct f, F_R. assert (e1 = negb e2). 
    destruct e1. destruct e2. simpl in H. discriminate. auto. rewrite <- H. auto.
    unfold rel, extractor. destruct t1, t2. destruct e2. 
    (* Case 1 *)
    simpl in H2. rewrite H2 in H0.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1. apply bool_eq_corr in H6.
    apply bool_eq_corr in H3. apply bool_eq_corr in H4. apply bool_eq_corr in H5.
    simpl in *. apply andb_true_iff. split. apply andb_true_iff; split; apply bool_eq_corr. 
    simpl in *. destruct s, s0. simpl in *. rewrite ADL.mod_dist_FMul2.
    rewrite mod_dist_Fadd. rewrite dot_assoc. rewrite mod_dist_Gdot. rewrite <- H0. rewrite H1.
    rewrite H3. rewrite <- dot_assoc. do 2 rewrite <- ADL.mod_dist_FMul2.
    rewrite <- mod_dist_Fadd. assert (x * f0 + Finv f0 * x = 0). field; auto.
    rewrite H7. rewrite mod_ann. rewrite one_right.
    rewrite <- ADL.mod_dist_FMul2. replace (x0/x0) with 1. rewrite mod_id. trivial.
    (* Number 2 *)
    field; auto. simpl. rewrite mod_dist_Fadd. rewrite dot_assoc. rewrite <- H5. rewrite H6.
    rewrite <- dot_assoc. rewrite <- mod_dist_Fadd. rewrite Ropp_def. rewrite mod_ann.
    rewrite one_right. trivial.
    (* Number 3 *)
    apply bool_eq_corr. destruct s, s0. simpl in *. rewrite ADL.mod_dist_FMul2.
    rewrite <- H3. rewrite H4. rewrite <- ADL.mod_dist_FMul2. replace (x0/x0) with 1.
    rewrite mod_id. trivial. field; auto.
    (* Case 2 *)
    simpl in H2. rewrite H2 in H0.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply andb_true_iff in H0. apply andb_true_iff in H1. destruct H0, H1.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1. apply bool_eq_corr in H6.
    apply bool_eq_corr in H3. apply bool_eq_corr in H4. apply bool_eq_corr in H5.
    simpl in *. apply andb_true_iff. split. apply andb_true_iff; split; apply bool_eq_corr. 
    simpl in *. destruct s, s0. simpl in *. rewrite ADL.mod_dist_FMul2.
    rewrite mod_dist_Fadd. rewrite dot_assoc. rewrite mod_dist_Gdot. rewrite <- H1.
    rewrite H0. rewrite H4. rewrite <- dot_assoc. do 2 rewrite <- ADL.mod_dist_FMul2.
    rewrite <- mod_dist_Fadd. assert (x0 * f + Finv f * x0 = 0). field; auto.
    rewrite H7. rewrite mod_ann. rewrite one_right.
    rewrite <- ADL.mod_dist_FMul2. replace (x/x) with 1. rewrite mod_id. trivial.
    (* Number 2 *)
    field; auto. simpl. rewrite mod_dist_Fadd. rewrite dot_assoc. rewrite <- H6. 
    rewrite H5. rewrite <- dot_assoc. rewrite <- mod_dist_Fadd. rewrite Ropp_def. 
    rewrite mod_ann. rewrite one_right. trivial.
    (* Number 3 *)
    apply bool_eq_corr. destruct s, s0. simpl in *. rewrite ADL.mod_dist_FMul2.
    rewrite <- H4. rewrite H3. rewrite <- ADL.mod_dist_FMul2. replace (x/x) with 1.
    rewrite mod_id. trivial. field; auto.
    (* Zero knowledge *)
    split. intros. simpl in *. unfold V1, P0, V0,
    simulator, simMap in *.
    destruct s, e. trivial. apply andb_true_iff in H.
    destruct H.  apply andb_true_iff in H.  destruct H.
    apply bool_eq_corr in H. apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    simpl in *. rewrite H. rewrite H0. rewrite H1. trivial. trivial.
    split; simpl; unfold simMapInv, simMap;
    destruct e; trivial; simpl in *. unfold R, T, Sec in *. destruct r, w.
    apply injective_projections; simpl. field; auto.
    apply eq_proj. destruct s0, s1. simpl. field; auto.
    apply injective_projections; simpl. field; auto.
    apply eq_proj. destruct t.2, w.2. simpl. field; auto.
    (* Simualtor corres *)
    simpl. unfold V1, simulator. destruct s, e; apply andb_true_iff; split. 
     apply andb_true_iff; split; apply bool_eq_corr; simpl; auto.
    apply bool_eq_corr; simpl; auto.
    apply andb_true_iff; split; apply bool_eq_corr; simpl; auto.
    apply bool_eq_corr; simpl; auto.
  Qed.    

  Lemma V1FreeLeft : forall c1 c1' c0  c t,
      V1 (c0,c1,c,false,t) = V1 (c0,c1',c,false,t).  
  Proof.
    intros. simpl. trivial.
  Qed.   

  Lemma V1FreeRight : forall c0 c0' c1 c t,
      V1 (c0,c1,c,true,t) = V1 (c0',c1,c,true,t).   
  Proof.
    intros. simpl. trivial.
  Qed. 

  Lemma simFreeRightCom : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).1.1.2  = (simulator (c0',c1) t true).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeRightResp : forall c0 c0' c1 t,
      (simulator (c0,c1) t false).2  = (simulator (c0',c1) t false).2.
  Proof.
    intros. simpl. trivial.
  Qed.  

  Lemma simFreeLeftCom : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).1.1.2  = (simulator (c0,c1') t false).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeLeftResp : forall c1 c1' c0 t,
      (simulator (c0,c1) t true).2  = (simulator (c0,c1') t true).2. 
  Proof.
    intros. simpl. trivial.
  Qed.

  End ElGamalSigmaKeyShift.

  (***  Abstact homomorphic encryption ***)
  Module Type EncryptionScheme.
    Parameter KGR : Type.                 (* randomness for keygen *)
    Parameter PK :  Type.                  (* public key space *)
    Parameter SK :  Type.                  (* secret key space *)

    Parameter M :   Set.           (* message space    *)
    Parameter Mop : M -> M -> M.  
    Parameter Mzero : M.     
    Parameter Mbool_eq : M -> M -> bool.
    Axiom M_monoids : Monoid M Mop Mzero Mbool_eq.

    Parameter C :   Set.           (* ciphertext space    *)
    Parameter Cop : C -> C -> C.  
    Parameter Czero : C.     
    Parameter Cbool_eq : C -> C -> bool.
    Axiom C_monoids : Monoid C Cop Czero Cbool_eq.
    
    Parameter R :   Set.           (* randomness space    *)
    Parameter Rop : R -> R -> R.  
    Parameter Rzero : R.     
    Parameter Rbool_eq : R -> R -> bool.
    Parameter Rinv : R -> R.
    Axiom R_group : Group R Rop Rzero Rbool_eq Rinv.

    Parameter keygen : KGR -> (PK*SK).    (* key generation   *)
    Definition keygenMix kgr := (keygen kgr).1. 
    Parameter enc : PK -> M -> R -> C.    (* encryption       *)
    Parameter dec : SK -> C -> M.         (* decryption       *)
    Parameter keymatch : PK -> SK -> bool. (* checks key consistence *)

    Axiom correct : forall (kgr : KGR)(m : M)(r : R),
                dec (keygen kgr).2 (enc (keygen kgr).1 m r) = m.

    Axiom homomorphism : forall (pk : PK)(m m' : M)(r r' : R),
                Cop (enc pk m r)(enc pk m' r') = 
                  enc pk (Mop m m') (Rop r r'). 

    (* This axiom may be unneccesary *)
    Axiom enc_id : forall (pk : PK),
      enc pk Mzero Rzero = Czero.
    
  End EncryptionScheme.

  Module Type AbstactReEncryption (ES : EncryptionScheme)  <: Function.
     Import ES.

     Parameter pk : PK.

     Definition Pub := C.
     Definition Sec := R.
     Definition Out := C.
     Definition dec := Cbool_eq.

     Definition Fun c r := Cop c (enc pk Mzero r).
  End AbstactReEncryption.


  Module AbstactReEncryptionSigma (ES : EncryptionScheme)
    (AR : AbstactReEncryption ES) <: SigmaOfFunction AR.
    Import ES.
    Import AR.

    Definition Stat := prod Pub Pub.
    Definition W := Sec. 

  (* Before publishing it would be nice to turn this into a module *)
  Definition Rel (stat : Stat)(w : W) := 
    dec (Fun stat.1 w) stat.2.
  Definition C := C.
  Definition R := R.
  Definition T := R.                              (* The set of responses  *)

 (** Begin Sigma Proper *)
  Definition P0 (stat : Stat)(r : ES.R)(w : W) : 
      (Stat*ES.C) :=
    let '(c0, c1) := stat in     
    (stat,Fun c0 r).

  Definition V0 (ggtoxgtor: Stat*C) (c: bool):
     (Stat*C*bool)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: Stat*C*bool) 
      (r x: R) : Stat*C*bool*T :=
        let '(c,a,e) := ggtoxgtorc in   
      (ggtoxgtorc, if e then Rop (Rinv x) r else r).

  Definition V1 (ggtoxgtorcs : Stat*C*bool*T) :=
    let '((c0,c1),a,c,t) := ggtoxgtorcs in   
    if c then dec a (Fun c1 t) else
      dec a (Fun c0 t).

  Definition simMap (s : Stat)(x : W)(c : bool)(r : T):=
    if c then Rop (Rinv x) r else r.

  Definition simMapInv (s : Stat)(x : W)(c : bool)(t :T):=
    if c then Rop x t else t.

  Definition simulator (stat :Stat)(t: T)(e : bool) :=
        let '(c0,c1) := stat in 
    if e then (stat,Fun c1 t,e,t) else 
    (stat,Fun c0 t,e,t).

  Definition extractor (s1 s2: T)(e1 e2 : bool) :=
    if e2 then Rop s1 (Rinv s2) else Rop s2 (Rinv s1).

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.

  Theorem SP
    :  SigmaProtocol Form. 
  Proof.
    pose M_monoids. pose C_monoids. pose R_group.
    constructor; intros; auto. apply BinGroup.module_abegrp.
    destruct s. auto.
    destruct sce, p. simpl. auto.
    simpl. unfold simulator. destruct s.
    destruct e; auto.  simpl. unfold simulator. 
    destruct s. destruct e; auto.
    simpl. unfold simulator. destruct s2.
    destruct s1. destruct e; auto.
    (* Correctness *)
    simpl. unfold V1, V0, P0. simpl in H.
    unfold rel in H. destruct s. destruct c. unfold Rel in H.
    simpl in H.
    apply bool_eq_corr; simpl; trivial.
    apply bool_eq_corr in H. 
    unfold Fun in *. simpl in *. rewrite <- H. 
    rewrite <- dot_assoc. apply f_equal2; auto. rewrite homomorphism.
    apply f_equal3; auto. symmetry. apply one_right. rewrite dot_assoc.
    rewrite <- inv_right. rewrite one_left. trivial.
    apply bool_eq_corr; simpl; trivial.
    (* Soundness *)
    simpl in *. unfold BinGroup.Gbool_eq in H.
    apply negb_true_iff in H. assert (e1 = negb e2). 
    destruct e1. destruct e2. simpl in H. discriminate. auto. rewrite <- H. auto.
    unfold Rel, extractor, Fun in *. destruct e2. 
    (* Case 1 *)
    simpl in H2. rewrite H2 in H0. destruct s.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1. 
    apply bool_eq_corr. simpl in *. replace Mzero with (Mop Mzero Mzero).
    rewrite <- homomorphism. rewrite dot_assoc. rewrite <- H0. rewrite H1.
    rewrite <- dot_assoc. rewrite homomorphism. rewrite one_right. 
    rewrite <- inv_right. rewrite enc_id. apply one_right. apply one_right.
    (* Case 2 *)
    simpl in H2. rewrite H2 in H0. destruct s.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    apply bool_eq_corr. simpl in *. replace Mzero with (Mop Mzero Mzero).
    rewrite <- homomorphism. rewrite dot_assoc. rewrite <- H1. rewrite H0.
    rewrite <- dot_assoc. rewrite homomorphism. rewrite one_right. 
    rewrite <- inv_right. rewrite enc_id. apply one_right. apply one_right.
    (* Zero knowledge *)
    split. intros. simpl in *. unfold V1, P0, V0,
    simulator, simMap in *.
    destruct s, e. apply bool_eq_corr in H. rewrite H. trivial. trivial.
    split; simpl; unfold simMapInv, simMap;
    destruct e; trivial; simpl in *. rewrite dot_assoc. rewrite <- inv_right.
    rewrite one_left. trivial.  rewrite dot_assoc. rewrite <- inv_left.
    apply one_left.
    (* Simualtor corres *)
    simpl. unfold V1, simulator. destruct s, e; apply bool_eq_corr; auto.
  Qed.    

  Lemma V1FreeLeft : forall c1 c1' c0  c t,
      V1 (c0,c1,c,false,t) = V1 (c0,c1',c,false,t).  
  Proof.
    intros. simpl. trivial.
  Qed.   

  Lemma V1FreeRight : forall c0 c0' c1 c t,
      V1 (c0,c1,c,true,t) = V1 (c0',c1,c,true,t).   
  Proof.
    intros. simpl. trivial.
  Qed. 

  Lemma simFreeRightCom : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).1.1.2  = (simulator (c0',c1) t true).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeRightResp : forall c0 c0' c1 t,
      (simulator (c0,c1) t false).2  = (simulator (c0',c1) t false).2.
  Proof.
    intros. simpl. trivial.
  Qed.  

  Lemma simFreeLeftCom : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).1.1.2  = (simulator (c0,c1') t false).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeLeftResp : forall c1 c1' c0 t,
      (simulator (c0,c1) t true).2  = (simulator (c0,c1') t true).2. 
  Proof.
    intros. simpl. trivial.
  Qed.

  End AbstactReEncryptionSigma.

  (***  Abstract homorphic commitment ***)
  Module Type CommitmentScheme.
    Parameter CK :  Type.                  (* commitment key space *)

    Parameter M :   Set.           (* message space    *)
    Parameter Mop : M -> M -> M.  
    Parameter Mzero : M.     
    Parameter Mbool_eq : M -> M -> bool.
    Axiom M_monoids : Monoid M Mop Mzero Mbool_eq.

    Parameter C :   Set.           (* commitment space    *)
    Parameter Cop : C -> C -> C.  
    Parameter Czero : C.     
    Parameter Cbool_eq : C -> C -> bool.
    Axiom C_monoids : Monoid C Cop Czero Cbool_eq.
    
    Parameter R :   Set.           (* opening space    *)
    Parameter Rop : R -> R -> R.  
    Parameter Rzero : R.     
    Parameter Rbool_eq : R -> R -> bool.
    Parameter Rinv : R -> R.
    Axiom R_group : Group R Rop Rzero Rbool_eq Rinv.

    Parameter commit : CK -> M -> R -> C.    (* encryption       *)
    Parameter open :   CK -> C -> M -> R -> bool. (* opening     *)

    Axiom correct : forall (ck : CK)(m : M)(r : R),
                open ck (commit ck m r) m r = true.

    Axiom homomorphism : forall (pk : CK)(m m' : M)(r r' : R),
                Cop (commit pk m r)(commit pk m' r') = 
                  commit pk (Mop m m') (Rop r r'). 

    (* This axiom may be unnecceary *)
    Axiom enc_id : forall (pk : CK),
      commit pk Mzero Rzero = Czero.
    
  End CommitmentScheme.

  Module Type AbstactReRandom (CS : CommitmentScheme)  <: Function.
     Import CS.

     Parameter pk : CK.

     Definition Pub := C.
     Definition Sec := R.
     Definition Out := C.
     Definition dec := Cbool_eq.

     Definition Fun c r := Cop c (commit pk Mzero r).
  End AbstactReRandom.


  Module AbstactReRandomSigma (CS : CommitmentScheme)
    (AR : AbstactReRandom CS) <: SigmaOfFunction AR.
    Import CS.
    Import AR.

    Definition Stat := prod Pub Pub.
    Definition W := Sec. 

  (* Before publishing it would be nice to turn this into a module *)
  Definition Rel (stat : Stat)(w : W) := 
    dec (Fun stat.1 w) stat.2.
  Definition C := C.
  Definition R := R.
  Definition T := R.                              (* The set of responses  *)

 (** Begin Sigma Proper *)
  Definition P0 (stat : Stat)(r : R)(w : W) : 
      (Stat*C) :=
    let '(c0, c1) := stat in     
    (stat,Fun c0 r).

  Definition V0 (ggtoxgtor: Stat*C) (c: bool):
     (Stat*C*bool)
    := (ggtoxgtor, c).

  Definition P1 (ggtoxgtorc: Stat*C*bool) 
      (r x: R) : Stat*C*bool*T :=
        let '(c,a,e) := ggtoxgtorc in   
      (ggtoxgtorc, if e then Rop (Rinv x) r else r).

  Definition V1 (ggtoxgtorcs : Stat*C*bool*T) :=
    let '((c0,c1),a,c,t) := ggtoxgtorcs in   
    if c then dec a (Fun c1 t) else
      dec a (Fun c0 t).

  Definition simMap (s : Stat)(x : W)(c : bool)(r : T):=
    if c then Rop (Rinv x) r else r.

  Definition simMapInv (s : Stat)(x : W)(c : bool)(t :T):=
    if c then Rop x t else t.

  Definition simulator (stat :Stat)(t: T)(e : bool) :=
        let '(c0,c1) := stat in 
    if e then (stat,Fun c1 t,e,t) else 
    (stat,Fun c0 t,e,t).

  Definition extractor (s1 s2: T)(e1 e2 : bool) :=
    if e2 then Rop s1 (Rinv s2) else Rop s2 (Rinv s1).

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.

  Theorem SP
    :  SigmaProtocol Form. 
  Proof.
    pose M_monoids. pose C_monoids. pose R_group.
    constructor; intros; auto. apply BinGroup.module_abegrp.
    destruct s. auto.
    destruct sce, p. simpl. auto.
    simpl. unfold simulator. destruct s.
    destruct e; auto.  simpl. unfold simulator. 
    destruct s. destruct e; auto.
    simpl. unfold simulator. destruct s2.
    destruct s1. destruct e; auto.
    (* Correctness *)
    simpl. unfold V1, V0, P0. simpl in H.
    unfold rel in H. destruct s. destruct c. unfold Rel in H.
    simpl in H.
    apply bool_eq_corr; simpl; trivial.
    apply bool_eq_corr in H. 
    unfold Fun in *. simpl in *. rewrite <- H. 
    rewrite <- dot_assoc. apply f_equal2; auto. rewrite homomorphism.
    apply f_equal3; auto. symmetry. apply one_right. rewrite dot_assoc.
    rewrite <- inv_right. rewrite one_left. trivial.
    apply bool_eq_corr; simpl; trivial.
    (* Soundness *)
    simpl in *. unfold BinGroup.Gbool_eq in H.
    apply negb_true_iff in H. assert (e1 = negb e2). 
    destruct e1. destruct e2. simpl in H. discriminate. auto. rewrite <- H. auto.
    unfold Rel, extractor, Fun in *. destruct e2. 
    (* Case 1 *)
    simpl in H2. rewrite H2 in H0. destruct s.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1. 
    apply bool_eq_corr. simpl in *. replace Mzero with (Mop Mzero Mzero).
    rewrite <- homomorphism. rewrite dot_assoc. rewrite <- H0. rewrite H1.
    rewrite <- dot_assoc. rewrite homomorphism. rewrite one_right. 
    rewrite <- inv_right. rewrite enc_id. apply one_right. apply one_right.
    (* Case 2 *)
    simpl in H2. rewrite H2 in H0. destruct s.
    apply bool_eq_corr in H0. apply bool_eq_corr in H1.
    apply bool_eq_corr. simpl in *. replace Mzero with (Mop Mzero Mzero).
    rewrite <- homomorphism. rewrite dot_assoc. rewrite <- H1. rewrite H0.
    rewrite <- dot_assoc. rewrite homomorphism. rewrite one_right. 
    rewrite <- inv_right. rewrite enc_id. apply one_right. apply one_right.
    (* Zero knowledge *)
    split. intros. simpl in *. unfold V1, P0, V0,
    simulator, simMap in *.
    destruct s, e. apply bool_eq_corr in H. rewrite H. trivial. trivial.
    split; simpl; unfold simMapInv, simMap;
    destruct e; trivial; simpl in *. rewrite dot_assoc. rewrite <- inv_right.
    rewrite one_left. trivial.  rewrite dot_assoc. rewrite <- inv_left.
    apply one_left.
    (* Simualtor corres *)
    simpl. unfold V1, simulator. destruct s, e; apply bool_eq_corr; auto.
  Qed.    

  Lemma V1FreeLeft : forall c1 c1' c0  c t,
      V1 (c0,c1,c,false,t) = V1 (c0,c1',c,false,t).  
  Proof.
    intros. simpl. trivial.
  Qed.   

  Lemma V1FreeRight : forall c0 c0' c1 c t,
      V1 (c0,c1,c,true,t) = V1 (c0',c1,c,true,t).   
  Proof.
    intros. simpl. trivial.
  Qed. 

  Lemma simFreeRightCom : forall c0 c0' c1 t,
      (simulator (c0,c1) t true).1.1.2  = (simulator (c0',c1) t true).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeRightResp : forall c0 c0' c1 t,
      (simulator (c0,c1) t false).2  = (simulator (c0',c1) t false).2.
  Proof.
    intros. simpl. trivial.
  Qed.  

  Lemma simFreeLeftCom : forall c1 c1' c0 t,
      (simulator (c0,c1) t false).1.1.2  = (simulator (c0,c1') t false).1.1.2.
  Proof.
    intros. simpl. trivial.
  Qed.

  Lemma simFreeLeftResp : forall c1 c1' c0 t,
      (simulator (c0,c1) t true).2  = (simulator (c0,c1') t true).2. 
  Proof.
    intros. simpl. trivial.
  Qed.

  End AbstactReRandomSigma.

End BasicSigmas.
