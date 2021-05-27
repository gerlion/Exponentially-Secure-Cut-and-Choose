Require Coq.Program.Tactics.
Require Import ssreflect ssrfun ssrbool.
From Groups Require Import groups module vectorspace.
Require Import Coq.Bool.Bool.
Require Import Field. 
Require Import Field_theory.
Require Import sigmaprotocol.

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

Module Type EncryptionScheme.

 Parameter KGR : Set.  

 Parameter PublicKey : Set.
 Parameter SecretKey : Set.

 Parameter Message : Set.
 Parameter Ciphertext : Set.
 Parameter Randomness : Set.

 Parameter mdec : Message -> Message -> bool.

 Parameter keygen : KGR -> PublicKey*SecretKey.   
 Parameter enc : PublicKey -> Message -> Randomness -> Ciphertext. 
 Parameter dec : PublicKey -> SecretKey -> Ciphertext -> Message.

 Parameter keymatch : PublicKey -> SecretKey -> bool.

 Axiom correct : forall (m: Message)(pk : PublicKey)(sk : SecretKey)(r : Randomness),
    keymatch pk sk = true ->
    dec pk sk (enc pk m r) = m.

 Axiom correctKeyMatch : forall (kgr : KGR),
    let '(pk,sk) := keygen kgr in
    keymatch pk sk = true.
    
End EncryptionScheme.

Module Type DistributedDecryption (ES : EncryptionScheme).
 Import ES.

 Parameter SecretKeyShare : Set.
 Parameter AuxData : Set.
 
 Parameter DecryptionShare : Set.

 Parameter dsdec : DecryptionShare -> DecryptionShare -> bool.

 Parameter DR : Set.

 Parameter Deal : PublicKey -> SecretKey -> DR -> SecretKeyShare*SecretKeyShare*AuxData. 
 Parameter Verify : PublicKey -> AuxData -> bool -> SecretKeyShare -> bool.
 Parameter Play : SecretKeyShare -> Ciphertext -> DecryptionShare.
 Parameter Reconstruct : Ciphertext -> DecryptionShare -> DecryptionShare -> Message. 

 Parameter FindKey : SecretKeyShare -> SecretKeyShare -> SecretKey.

 Axiom Correctness : forall (m: Message)(kgr : KGR)(r : Randomness)(dr : DR),
   let '(pk,sk) := keygen kgr in
   let c := enc pk m r in
   let '(sk0, sk1, aux) := Deal pk sk dr in
   Verify pk aux false sk0 = true /\ Verify pk aux true sk1 = true /\ 
  Reconstruct c (Play sk0 c) (Play sk1 c) = m.

 Axiom Integrity : forall (m: Message)(pk : PublicKey)(sk0 sk1 : SecretKeyShare)
   (aux : AuxData)(r : Randomness),
    let c := enc pk m r in
    Verify pk aux false sk0 = true ->
    Verify pk aux true sk1 = true ->
    Reconstruct c (Play sk0 c) (Play sk1 c) = m /\ keymatch pk (FindKey sk0 sk1).

 Parameter DealSim : PublicKey -> DR -> bool -> SecretKeyShare*AuxData.
 Parameter PlaySim : PublicKey -> SecretKeyShare -> Ciphertext -> Message ->
   DecryptionShare.
 Parameter DealSimMap : PublicKey -> SecretKey -> DR -> bool -> DR.
 Parameter DealSimMapInv : PublicKey -> SecretKey -> DR -> bool -> DR.

 Axiom Simulatability : forall (kgr : KGR)(i : bool)(c : Ciphertext)(m : Message)(dr : DR),
    let '(pk,sk) := keygen kgr in
    dec pk sk c = m ->
    let '(sk0, sk1, aux) := Deal pk sk dr in
    if i then (sk1,aux) = DealSim pk (DealSimMap pk sk dr i) i /\ 
                              Play sk0 c = PlaySim pk sk1 c m
    else (sk0,aux) = DealSim pk (DealSimMap pk sk dr i) i /\ Play sk1 c = 
      PlaySim pk sk0 c m.
  
 Axiom SimMapBijection : forall (kgr : KGR)(dr : DR)(i : bool),
    let '(pk,sk) := keygen kgr in
    DealSimMapInv pk sk (DealSimMap pk sk dr i) i = dr /\
          DealSimMap pk sk (DealSimMapInv pk sk dr i) i = dr.

End DistributedDecryption.

Module ProofOfDecryption (ES : EncryptionScheme)(DD : DistributedDecryption ES).
    Import ES.
    Import DD.

    Definition Stat := prod (prod PublicKey Ciphertext) Message.
    Definition W := SecretKey .                          
    Definition Rel (s : Stat)(r : W) := keymatch s.1.1 r && 
      mdec (dec s.1.1 r s.1.2) s.2.
    Definition C := prod (prod AuxData DecryptionShare) DecryptionShare.
    Definition R := DR.
    Definition T := SecretKeyShare. 

    Definition P0 (s : Stat)(r : R)(w : W)  : (Stat*C) :=
      let '(sk0, sk1, aux) := Deal s.1.1 w r in
      (s,(aux,(Play sk0 s.1.2),(Play sk1 s.1.2))).

    Definition V0 (s : Stat*C)(e : bool) : (Stat*C*bool) := (s,e).  

    Definition P1 (sce : Stat*C*bool)(r : R)(w : W) :(Stat*C*bool*T) :=
      let '(s, c, e) := sce in
      let '(sk0, sk1, aux) := Deal s.1.1 w r in
      if sce.2 then (sce,sk1) else (sce,sk0).

    Definition V1 (scet : Stat*C*bool*T) : bool :=       
      let '(s, c, e, t) := scet in
      Verify s.1.1 c.1.1 e t && (if e then dsdec (Play t s.1.2) c.2 else 
        dsdec (Play t s.1.2) c.1.2) && mdec (Reconstruct s.1.2 c.1.2 c.2) s.2.
    
    Definition simulator (s : Stat)(t : T)(e : bool) : (Stat*C*bool*T) :=
       let '(ski, aux) := DealSim s.1.1 t e in
       if e then (aux,  else .
    Definition simMap    : Stat -> W -> bool -> R -> T. admit. Admitted.
    Definition simMapInv : Stat -> W -> bool -> T -> R. admit. Admitted.
    Definition extractor : T -> T -> bool -> bool -> W. admit. Admitted.

    Definition Form : Sigma.form bool := Sigma.mkForm Rel BinGroup.Gdot 
    BinGroup.Gone BinGroup.Ginv BinGroup.Gbool_eq (fun a b => negb (BinGroup.Gbool_eq a b))
    P0 V0 P1 V1 simulator simMap 
    simMapInv extractor.
  
    Lemma SP : SigmaProtocol Form.
    Proof.
      constructor; intros; unfold P0, V0, P1, V1 in *; simpl; trivial. 
      apply BinGroup.module_abegrp. unfold P0. destruct (Deal s.1.1 w r).
      destruct p. simpl. trivial. unfold P1. destruct sce. destruct p. 
      destruct (Deal s.1.1 w r). destruct p. destruct b; simpl; trivial.
    Qed.
End Module.

Module Type ElGamal (Group : GroupSig)(Field : FieldSig)(VS : VectorSpaceSig Group Field) <: EncryptionScheme.
  Import Field.
  Import Group.
  Import VS.

 Module VSAL := VectorSpaceAddationalLemmas Group Field VS.
  Import VSAL.

 Definition KGR := prod G F.  

 Definition PublicKey := prod G G.
 Definition SecretKey := F.

 Definition Message := G.
 Definition Ciphertext := prod G G.
 Definition Randomness := F.

 Definition keygen (kgr : KGR) := ((kgr.1,kgr.1^kgr.2),kgr.2). 
 Definition enc (pk : PublicKey)(m : Message)(r : Randomness) := (pk.1^r,pk.2^r o m). 
 Definition dec (pk : PublicKey)(sk : SecretKey)(c : Ciphertext) := (c.2 o - c.1^sk).

 Definition keymatch (pk :  PublicKey)(sk : SecretKey) := Gbool_eq (pk.1^sk) pk.2.

 Lemma correct : forall (m: Message)(pk : PublicKey)(sk : SecretKey)(r : Randomness),
    keymatch pk sk = true ->
    dec pk sk (enc pk m r) = m.
 Proof.
    pose Group.module_abegrp.
    intros. unfold dec, enc, keymatch in *. simpl. apply bool_eq_corr in H.
    rewrite <- H. rewrite <- mod_dist_Fmul. rewrite mod_dist_FMul2. rewrite comm.
    rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
 Qed.

 Lemma correctKeyMatch : forall (kgr : KGR),
    let '(pk,sk) := keygen kgr in
    keymatch pk sk = true.
 Proof.
  pose Group.module_abegrp.
  intros. unfold keymatch. simpl. apply bool_eq_corr. trivial.
 Qed.
 
End ElGamal.

Module DDElGamal (Group : GroupSig)(Field : FieldSig)(VS : VectorSpaceSig Group Field) 
  (EG : ElGamal Group Field VS) <: DistributedDecryption EG.
  Import Group.
  Import Field.
  Import VS.
  Import EG.
  Module VSAL := VectorSpaceAddationalLemmas Group Field VS.
  Import VSAL.

  Definition SecretKeyShare := F.
  Definition AuxData := prod G G.
  Definition DecryptionShare := G.
  Definition DR := F.

  Definition Deal (pk : PublicKey)(sk : SecretKey)(dr : DR) :=
   (dr,sk-dr,(pk.1^dr,pk.1^(sk-dr))). 

  Definition Verify (pk : PublicKey)(aux : AuxData)(l : bool)(sk : SecretKeyShare) :=
    Gbool_eq pk.2 (aux.1 o aux.2) && 
      if l then Gbool_eq aux.2 (pk.1^sk) else Gbool_eq aux.1 (pk.1^sk).
  Definition Play (sk : SecretKeyShare)(c : Ciphertext) := c.1^sk.
  Definition Reconstruct (c : Ciphertext)(ds0 : DecryptionShare)
    (ds1 : DecryptionShare) := c.2 o -(ds0 o ds1).

  Definition FindKey (sk0 sk1 : SecretKeyShare) := sk0 + sk1.

 Lemma Correctness : forall (m: Message)(kgr : KGR)(r : Randomness)(dr : DR),
   let '(pk,sk) := keygen kgr in
   let c := enc pk m r in
   let '(sk0, sk1, aux) := Deal pk sk dr in
   Verify pk aux false sk0 = true /\ Verify pk aux true sk1 = true /\ 
  Reconstruct c (Play sk0 c) (Play sk1 c) = m.
 Proof.
  pose Group.module_abegrp. intros. unfold Verify, Reconstruct, Play. split. 
  simpl. apply andb_true_iff. split. apply bool_eq_corr. rewrite <- mod_dist_Fadd.
  apply f_equal.  field; auto. apply bool_eq_corr. trivial. split. simpl.
  apply andb_true_iff. split. apply bool_eq_corr. rewrite <- mod_dist_Fadd.
  apply f_equal. field; auto. apply bool_eq_corr. trivial.
  (* Reconstruct *) simpl.
  rewrite <- mod_dist_Fadd. replace (dr + (kgr.2 - dr)) with kgr.2.
  rewrite <- mod_dist_Fmul. rewrite <- mod_dist_FMul2. rewrite comm. 
  rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
  field; auto.
 Qed.

 Lemma Integrity : forall (m: Message)(pk : PublicKey)(sk0 sk1 : SecretKeyShare)
   (aux : AuxData)(r : Randomness),
    let c := enc pk m r in
    Verify pk aux false sk0 = true ->
    Verify pk aux true sk1 = true ->
    Reconstruct c (Play sk0 c) (Play sk1 c) = m  /\ keymatch pk (FindKey sk0 sk1).
 Proof.
  pose Group.module_abegrp. split.
  intros. unfold Reconstruct, Play, Verify in *. simpl in *.  
  apply andb_true_iff in H. apply andb_true_iff in H0. destruct H. destruct H0.
  apply bool_eq_corr in H2. apply bool_eq_corr in H0. apply bool_eq_corr in H1.
  do 2 rewrite <- mod_dist_Fmul. do 2 rewrite mod_dist_FMul2. rewrite <- mod_dist_Gdot.
  rewrite <- H1. rewrite <- H2. rewrite <- H0. rewrite comm. 
  rewrite dot_assoc. rewrite <- inv_left. rewrite one_left. trivial.
  unfold keymatch, Verify, FindKey in *.  apply andb_true_iff in H. 
  apply andb_true_iff in H0. destruct H. destruct H0.
  apply bool_eq_corr in H2. apply bool_eq_corr in H0. apply bool_eq_corr.
   rewrite H0. rewrite H2. apply bool_eq_corr in H1. rewrite H1. 
  rewrite mod_dist_Fadd. trivial.
 Qed.

 Definition DealSim (pk : PublicKey)(dr : DR)(l : bool) := 
  (dr,if l then (pk.2 o - pk.1^dr,pk.1^dr) else (pk.1^dr, pk.2 o - pk.1^dr)).
 Definition PlaySim (pk : PublicKey)(sk : SecretKeyShare)(c : Ciphertext)(m : Message)
     := c.2 o - (c.1^sk o m).
 Definition DealSimMap (pk : PublicKey)(sk : SecretKey)(dr : DR)(l : bool) 
    := if l then sk-dr else dr.
 Definition DealSimMapInv (pk : PublicKey)(sk : SecretKey)(dr : DR)(l : bool) := 
    if l then sk-dr else dr.

 Lemma Simulatability : forall (kgr : KGR)(i : bool)(c : Ciphertext)(m : Message)(dr : DR),
    let '(pk,sk) := keygen kgr in
    dec pk sk c = m ->
    let '(sk0, sk1, aux) := Deal pk sk dr in
    if i then (sk1,aux) = DealSim pk (DealSimMap pk sk dr i) i /\ 
                              Play sk0 c = PlaySim pk sk1 c m
    else (sk0,aux) = DealSim pk (DealSimMap pk sk dr i) i /\ 
                              Play sk1 c = PlaySim pk sk0 c m.
 Proof.
  pose Group.module_abegrp.
  intros. simpl. intros. unfold DealSim, DealSimMap, Play, PlaySim. destruct i.
  (* left *)
  split. apply injective_projections; simpl. trivial. apply injective_projections; 
  simpl. rewrite neg_eq. rewrite <- mod_dist_Fadd. apply f_equal. unfold DR in *.
  field; auto. trivial. unfold dec in H. rewrite <- H. pose inv_dist. symmetry in e.
  rewrite e. rewrite dot_assoc. rewrite comm. rewrite e. rewrite <- dob_neg. 
  rewrite (comm (- c.2) (c.1 ^ kgr.2)). rewrite dot_assoc. rewrite comm.
  do 2 rewrite dot_assoc. rewrite neg_eq. rewrite <- mod_dist_Fadd. rewrite <- dot_assoc.
  rewrite <- inv_left. rewrite one_right. apply f_equal. unfold DR in *. field; auto.
  (* right *)
  split. apply injective_projections; simpl. trivial. apply injective_projections; 
  simpl. trivial. rewrite neg_eq. rewrite <- mod_dist_Fadd. apply f_equal.
  unfold DR in *. field; auto. unfold dec in H. rewrite <- H. pose inv_dist. 
  symmetry in e. rewrite e. rewrite dot_assoc. rewrite comm. rewrite e. 
  rewrite <- dob_neg. rewrite (comm (- c.2) (c.1 ^ kgr.2)). rewrite dot_assoc.  
  rewrite comm. do 2 rewrite dot_assoc. rewrite neg_eq. rewrite <- mod_dist_Fadd.
  rewrite <- dot_assoc. rewrite <- inv_left. rewrite one_right. apply f_equal. 
  unfold DR in *. field; auto.
 Qed.
  
 Lemma SimMapBijection : forall (kgr : KGR)(dr : DR)(i : bool),
    let '(pk,sk) := keygen kgr in
    DealSimMapInv pk sk (DealSimMap pk sk dr i) i = dr /\
          DealSimMap pk sk (DealSimMapInv pk sk dr i) i = dr.
  Proof.
    intros. unfold DealSimMap, DealSimMapInv. simpl. destruct i; split; trivial.
    field; auto. field; auto. 
  Qed.

End DDElGamal.