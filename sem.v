Require Import Zee.lattice.
Require Import Zee.lang.

Require Import Zee.dec Zee.vals Zee.frame Zee.maplike.
Require Import Arith List Coq.Program.Basics Coq.Lists.ListSet Lia Coq.ZArith.BinInt.
Require Import Coq.Classes.RelationClasses.

Section Sem.
  Context {A : Set} {BinOpS : Set} `{lattice A}.
  Definition Lab := @Lab A.
  Definition Ty := @Ty A.
  Definition LabVar := @LabVar A.
  Definition SecTy := @SecTy A.
  Definition SecTyV := @SecTyV A.
  Definition AtomSecTy := @AtomSecTy A.
  Definition Cmd := @Cmd A BinOpS.
  Definition Expr := @Expr A BinOpS.
  Definition V := @V A.

  Context {δ : string -> option Z}.
  Context {F: string -> option (list (string * Lab) *
                               list (string * Lab) *
                               list (string * SecTy) * Lab * Lab * Cmd) }.
  Context {eval_binop: BinOpS -> V -> V -> V}.
  Context {VarT ArgT LocT MemT : Type} {H_var_finmaplike: FinMapLike VarT string (A + SecTyV)} {H_arg_finmaplike: FinMapLike ArgT string SecTyV} {H_loc_finmaplike: FinMapLike LocT string SecTyV} {H_mem_maplike: MapLike MemT nat V}.
  Definition Frame := @Frame A VarT ArgT LocT MemT _ _ _ _.
  Definition PFrame := @PFrame A VarT ArgT LocT _ _ _.
  Definition EFrame := @EFrame A MemT _.
  
  Notation "'〚' o '〛'" := (eval_binop o).
  
  Definition Stk := list Frame.
  Hint Unfold Stk.
 
  Global Instance HasRange_Stk : HasRange Stk := {}.
  exact (fun stk =>
           let fix visit stk m :=
               match stk with
                 nil => m
               | fr :: stk' => visit stk' (sp_of (eframe_of fr))
               end
           in match stk with
                nil => (0, 0)
              | fr :: stk' => (fp_of (eframe_of fr), visit stk (sp_of (eframe_of fr)))
              end).
  Defined.

  Global Instance ReadableMapLike_Stk : ReadableMapLike Stk nat V := {}.
  - exact (fun stk a =>
             let fix look stk :=
                 match stk with
                   nil => None
                 | fr :: stk' =>
                   match fr ? a with
                     Some v => Some v
                   | None => look stk'
                   end
                 end
             in look stk).
  - exact nil.
  - intros.
    simpl.
    reflexivity.
  Defined.

  Inductive ecfg := make_ecfg
                      {
                        expr_of: Expr;
                        ecfg_fr: Frame
                      }.
  
  Inductive scfg := make_scfg
                      {
                        secty_of: SecTy;
                        scfg_fr: PFrame
                      }.

  Inductive acfg := make_acfg
                      {
                        asecty_of: AtomSecTy;
                        ascfg_fr: PFrame
                      }.

  Inductive tcfg := make_tcfg
                      {
                        ty_of: Ty;
                        tcfg_fr: PFrame
                      }.

  Inductive kcfg := make_kcfg
                      {
                        lab_of: Lab;
                        kcfg_fr: PFrame
                      }.
  Hint Constructors ecfg scfg acfg tcfg.

  Notation "'⟨' e ',' fr '⟩ₑ'" := (make_ecfg e fr).
  Notation "'⟨' s ',' pfr '⟩ₛ'" := (make_scfg s pfr).
  Notation "'⟨' a ',' pfr '⟩ₐ'" := (make_acfg a pfr).
  Notation "'⟨' t ',' pfr '⟩ₜ'" := (make_tcfg t pfr).
  Notation "'⟨' k ',' pfr '⟩ₖ'" := (make_kcfg k pfr).
  
  Reserved Notation "kcfg '⇓ₖ' ℓ" (at level 80).
  
  Inductive EvalLab: kcfg -> A -> Prop :=
  | ElabVar κ ℓ pfr:
      ⟨LabVar κ, pfr⟩ₖ ⇓ₖ ℓ
  | ElabLit ℓ pfr:
      ⟨Lit ℓ, pfr⟩ₖ ⇓ₖ ℓ
  | ELabJoin k1 k2 ℓ1 ℓ2 pfr:
      ⟨k1, pfr⟩ₖ ⇓ₖ ℓ1 ->
      ⟨k2, pfr⟩ₖ ⇓ₖ ℓ2 ->
      ⟨Join k1 k2, pfr⟩ₖ ⇓ₖ (ℓ1 ⊔ ℓ2)
  | ELabMeet k1 k2 ℓ1 ℓ2 pfr:
      ⟨k1, pfr⟩ₖ ⇓ₖ ℓ1 ->
      ⟨k2, pfr⟩ₖ ⇓ₖ ℓ2 ->
      ⟨Meet k1 k2, pfr⟩ₖ ⇓ₖ (ℓ1 ⊓ ℓ2)
  where "kcfg '⇓ₖ' ℓ" := (EvalLab kcfg ℓ).
  Hint Constructors EvalLab.

  Reserved Notation "tcfg '⇓ₜ' π" (at level 80).
  Reserved Notation "scfg '⇓ₛ' τ" (at level 80).
  Reserved Notation "ecfg '⇓ₑ' τ" (at level 80).
  Reserved Notation "scfg '⇓ₐ' π" (at level 80).

  Fixpoint prodSecTyV (τ1 : SecTyV) (τ2 : SecTyV) : SecTyV :=
    match τ1 with
      ASTyV a => ProdSecTyV a τ2
    | ProdSecTyV a τ => ProdSecTyV a (prodSecTyV τ τ2)
    | NilTyV => τ2
    end.
  
  Fixpoint prodSecTyVlist (τs : list SecTyV) : SecTyV :=
    match τs with
      nil => NilTyV
    | τ :: τs' => prodSecTyV τ (prodSecTyVlist τs')
    end.
  
  Global Instance Raiseable_SecTyV : Raiseable SecTyV A := {}.
  Proof.
    intros τ ℓ.
    destruct τ.
    - destruct a.
      eapply ASTyV.
      constructor.
      + assumption.
      + eapply (a ⊔ ℓ).
      + constructor.
        eapply NonSecTyV.
    - eapply (ProdSecTyV a τ).
    - eapply NilTyV.
  Defined.
  
  Inductive EvalTy: tcfg -> TyV -> Prop :=
  | ETyInt pfr: ⟨IntTy, pfr⟩ₜ ⇓ₜ IntTV
  | ETyPtr k s pfr ℓ τ:
      ⟨k, pfr⟩ₖ ⇓ₖ ℓ ->
      ⟨s, pfr⟩ₛ ⇓ₛ τ ->
      ⟨PtrTy k s, pfr⟩ₜ ⇓ₜ (PtrTV ℓ τ)
  | ETySPtr s1 s2 pfr τ1 τ2:
      ⟨s1, pfr⟩ₛ ⇓ₛ τ1 ->
      ⟨s2, pfr⟩ₛ ⇓ₛ τ2 ->
      ⟨SPtrTy s1 s2, pfr⟩ₜ ⇓ₜ (SPtrTV τ1 τ2)
  | ETyExTy α k s pfr: ⟨ExTyTy α k s, pfr⟩ₜ ⇓ₜ (ExTyTV α s)
  | ETyExLab κ k s pfr: ⟨ExLabTy κ k s, pfr⟩ₜ ⇓ₜ (ExLabTV κ s)
  | ETyRec k s x pfr: ⟨RecTy k x s, pfr⟩ₜ ⇓ₜ (RecTyV x s)
  | ETySizeOf s pfr: ⟨SizeTy s, pfr⟩ₜ ⇓ₜ IntTV
  where "tcfg '⇓ₜ' π" := (EvalTy tcfg π)
  with EvalSecTy: scfg -> SecTyV -> Prop :=
       | ESecTySecTy a pfr τ:
           ⟨a, pfr⟩ₐ ⇓ₐ τ ->
           ⟨ASecTy a, pfr⟩ₛ ⇓ₛ τ
       | ESecTyProd τ1 τ2 (s1 : AtomSecTy) s2 pfr:
           ⟨s1, pfr⟩ₐ ⇓ₐ τ1 ->
           ⟨s2, pfr⟩ₛ ⇓ₛ τ2 ->
           ⟨ProdTy s1 s2, pfr⟩ₛ ⇓ₛ (prodSecTyV τ1 τ2)
       | ESecNilTy pfr:
           ⟨NilTy, pfr⟩ₛ ⇓ₛ NilTyV
  where "scfg '⇓ₛ' τ" := (EvalSecTy scfg τ)
  with EvalAtomSecTy: acfg -> SecTyV -> Prop :=
       | EAtomSecTySecTy t pfr π k ℓ:
           ⟨t, pfr⟩ₜ ⇓ₜ π ->
           ⟨k, pfr⟩ₖ ⇓ₖ ℓ ->
           ⟨STy t k, pfr⟩ₐ ⇓ₐ (STyV π ℓ)
       | ESecTyVar α k τ ℓ pfr:
           pfr ? α = Some (inr τ) ->
           ⟨k, pfr⟩ₖ ⇓ₖ ℓ ->
           ⟨VarTy α k, pfr⟩ₐ ⇓ₐ (τ ^^ ℓ)
  where "scfg ⇓ₐ π" := (EvalAtomSecTy scfg π).
  Hint Constructors EvalTy EvalSecTy EvalAtomSecTy.

  Fixpoint sizeOf (τ : SecTyV) : option nat :=
    match τ with
    | ASTyV _ => Some 1
    | ProdSecTyV _ τ' =>
      match sizeOf τ' with
      | Some n => Some (S n)
      | None => None
      end
    | NilTyV => Some 0
    end.

  Coercion Z.of_nat: nat >-> Z.
  
  Definition addr_of {X : Type} `{HasRange X} (n : Z) (x : X) : nat :=
    Z.to_nat (n + fp_of x).
  Hint Unfold addr_of.
  
  Inductive EvalExpr: ecfg -> V -> Prop :=
  | ENum n fr: ⟨Num n, fr⟩ₑ ⇓ₑ VNum n
  | EVar x fr v n:
      δ x = Some n ->
      fr ? addr_of n fr = Some v ->
      ⟨Var x, fr⟩ₑ ⇓ₑ v
  | EBinOp e1 e2 v1 v2 o fr:
      ⟨e1, fr⟩ₑ ⇓ₑ v1 ->
      ⟨e2, fr⟩ₑ ⇓ₑ v2 ->
      ⟨BinOp o e1 e2, fr⟩ₑ ⇓ₑ (〚o〛 v1 v2)
  | ESizeOf s fr τ n:
      ⟨s, pframe_of fr⟩ₛ ⇓ₛ τ ->
      sizeOf τ = Some n ->
      ⟨SizeOf s, fr⟩ₑ ⇓ₑ VNum n
  | EPackTy s1 s2 fr α τ e v k:
      ⟨s1, pframe_of fr⟩ₛ ⇓ₛ τ ->
      ⟨e, fr⟩ₑ ⇓ₑ v ->
      ⟨PackTy s1 e k α s2, fr⟩ₑ ⇓ₑ ExTy τ v
  | EPackLab k1 k2 fr ℓ κ v e s:
      ⟨k1, pframe_of fr⟩ₖ ⇓ₖ ℓ ->
      ⟨e, fr⟩ₑ ⇓ₑ v ->
      ⟨PackLab k1 e k2 κ s, fr⟩ₑ ⇓ₑ ExLab ℓ v
  | EUnroll e fr v:
      ⟨e, fr⟩ₑ ⇓ₑ v ->
      ⟨Unroll e, fr⟩ₑ ⇓ₑ v
  | ERoll e fr v:
      ⟨e, fr⟩ₑ ⇓ₑ v ->
      ⟨Roll e, fr⟩ₑ ⇓ₑ v
  | EAddrOf x fr n:
      δ x = Some n ->
      ⟨AddrOf x, fr⟩ₑ ⇓ₑ (VAddr (addr_of n fr) (version fr))
  where "ecfg '⇓ₑ' v" := (EvalExpr ecfg v).
  Hint Constructors EvalExpr.
    
  Inductive cfg := make_cfg
                     {
                       cmd_of: Cmd;
                       stck_of: Stk;
                       time_of: nat;
                       ver_of: Version
                     }.
  Hint Constructors cfg.
  Notation "'⟨' c ',' stk ',' q ',' ν '⟩'" := (make_cfg c stk q ν).

  Fixpoint matches (τ : SecTyV) (p : SecPat) : bool :=
    match p with
      PNil =>
      match τ with
        NilTyV => true
      | _ => false
      end
    | PProd ap p =>
      match τ with
        ProdSecTyV a τ => atomMatches a ap && matches τ p
      | _ => false
      end
    | PAtom ap =>
      match ap with
        PVar _ => true
      | ap => match τ with
               ASTyV a => atomMatches a ap
             | _ => false
             end
      end
    end with
  atomMatches (τ : AtomSecTyV) (ap : AtomPat) : bool :=
    match τ with
      STyV π _ =>
      match ap with
        SPat p _ =>
        match π, p with
          IntTV, PInt => true
        | SPtrTV τ1 τ2, PSPtr p1 p2 =>
          matches τ1 p1 && matches τ2 p2
        | PtrTV _ τ, PPtr _ p => matches τ p
        | _, _ => false
        end
      | PVar _ => true
      end
    | NonSecTyV => false
    end.
  
  Infix "≲" := matches (at level 70).

  Lemma var_matches_all:
    forall τ n,
      τ ≲ (PVar n) = true.
  Proof.
    intros.
    destruct τ; reflexivity.
  Qed.
  Hint Resolve var_matches_all.
  
  Fixpoint find_match (τ : SecTyV) (pats : list (SecPat * Cmd)) : option (SecPat * Cmd) :=
    match pats with
      nil => None
    | (p, c) :: pats' =>
      if (matches τ p) then Some (p, c)
      else find_match τ pats'
    end.
  
  Fixpoint close (p : SecPat) (τ : SecTyV) (pfr : PFrame) : option PFrame :=
    match p with
      PAtom ap =>
      match τ with
        ASTyV π => atomClose ap π pfr
      | _ => match ap with
              PVar α => Some (pfr [α ↦ inr τ])
            | _ => None
            end
      end
    | PProd ap p =>
      match τ with
        ProdSecTyV a τ =>
        match atomClose ap a pfr with
          Some pfr' => close p τ pfr'
        | None => None
        end
      | _ => None
      end
    | PNil => Some pfr
    end
  with atomClose (ap : AtomPat) (π : AtomSecTyV) (pfr : PFrame) : option PFrame :=
         match ap with
           SPat p κ =>
           match π with
             STyV ι ℓ =>
             match p, ι with
               PInt, IntTV => Some (pfr [κ ↦ inl ℓ])
             | PSPtr p1 p2, SPtrTV τ1 τ2 =>
               match close p1 τ1 pfr with
                 Some pfr' =>
                 match close p2 τ2 pfr' with
                   Some pfr'' => Some (pfr'' [κ ↦ inl ℓ])
                 | None => None
                 end
               | None => None
               end
             | PPtr x p1, PtrTV ℓ1 τ =>
               match close p1 τ pfr with
                 Some pfr' => Some (pfr' [x ↦ inl ℓ1] [κ ↦ inl ℓ])
               | None => None
               end
             | _, _ => None
             end
           | NonSecTyV => None
           end
         | PVar α => Some (pfr [α ↦ inr (ASTyV π)])
         end.

  Lemma invert_find_match:
    forall τ p pats c,
      find_match τ pats = Some (p, c) ->
      exists pats1 pats2, pats = pats1 ++ (p, c) :: pats2 /\ τ ≲ p = true.
  Proof.
    intros.
    induction pats; intros.
    - discriminate.
    - destruct a.
      cbn in *.      
      destruct (τ ≲ s) eqn:?H.
      + inversion H; subst; clear H.
        exists nil; exists pats.
        firstorder.
      + destruct (IHpats H) as [pats1 [pats2 [? ?]]].
        subst.
        clear IHpats.
        exists ((s, c0) :: pats1); exists pats2.
        split; eauto.
  Qed.

  Lemma invert_match_prod:
    forall τ a p,
      (τ ≲ PProd a p) = true ->
      exists ap τ', τ = ProdSecTyV ap τ' /\ ap ≲ a = true /\ τ' ≲ p = true.
  Proof.
    intros.
    induction τ.
    - discriminate.
    - exists a0; exists τ.
      split; eauto.
      simpl in * |-.
      split.
      + symmetry in H.
        eapply Bool.andb_true_eq in H.
        destruct a; easy.
      + symmetry in H.
        eapply Bool.andb_true_eq in H.
        easy.
    - simpl in *.
      discriminate.
  Qed.
  
  Lemma match_is_sound: forall τ (p : SecPat) fr,
      (τ ≲ p = true -> exists fr', close p τ fr = Some fr')
  with atom_match_is_sound: forall (π : AtomSecTyV) (pat : AtomPat) fr,
      (π ≲ pat = true -> exists fr', atomClose pat π fr = Some fr').
  Proof.
    - intros.
      revert τ H fr.
      induction p.
      + intros.
        eapply invert_match_prod in H.
        destruct H as [ap [τ' [? [? ?]]]].
        subst.
        simpl.
        destruct (atom_match_is_sound ap a fr H1) as [fr' ?].
        destruct (IHp τ' H2 fr') as [fr'' ?].
        exists fr''.
        rewrite -> H.
        assumption.
      + intros.
        destruct τ; try discriminate.
        exists fr.
        reflexivity.
      + intros.
        cbn.
        destruct τ.
        * eapply atom_match_is_sound.
          assumption.
        * cbn in *.
          destruct a; try discriminate.
          eexists.
          reflexivity.
        * destruct a; try discriminate.
          eexists.
          reflexivity.
    - intros.
      induction pat.
      + cbn.
        destruct π; try discriminate.
        * destruct p; cbn in *.
          -- destruct t; (eexists; reflexivity) || discriminate.
          -- destruct t; cbn in *; try discriminate.
             assert (s2 ≲ s0 = true).
             {
               destruct (s2 ≲ s0); reflexivity || discriminate.
             }
             assert (s3 ≲ s1 = true).
             {
               destruct (s3 ≲ s1); try reflexivity.
               rewrite -> H1 in *.
               discriminate.
             }
             destruct (match_is_sound _ _ fr H1) as [fr' ?].
             simpl.
             rewrite -> H3.
             destruct (match_is_sound _ _ fr' H2) as [fr'' ?].
             rewrite -> H4.
             eexists.
             reflexivity.
          -- destruct t; try discriminate.
             destruct (match_is_sound _ _ fr H) as [fr' ?].
             rewrite -> H1.
             eexists. reflexivity.
      + eexists.
        reflexivity.
  Qed.

  Definition set_union := @set_union _ string_dec.
  Definition set_add := @set_add _ string_dec.
  Definition empty_set := empty_set string.
  
  Fixpoint vars (c : Cmd) : set string :=
    match c with
      CSkip => empty_set
    | CLet x _ _ c => set_add x (vars c)
    | CIf _ c1 c2 => set_union (vars c1) (vars c2)
    | CWhile _ c => vars c
    | CSeq c1 c2 => set_union (vars c1) (vars c2)
    | CWrite _ _ => empty_set
    | CRead _ _ => empty_set
    | CAt _ _ c => vars c
    | CLabIf _ _ c1 c2 => set_union (vars c1) (vars c2)
    | CMatch _ arms => fold_right (fun p => set_union (vars (snd p))) empty_set arms
    | CFP _ => empty_set
    | CCall _ _ _ _ => empty_set
    | CUnpTy _ _ x _ _ c => set_add x (vars c)
    | CUnpLab _ _ x _ _ c => set_add x (vars c)
    | CDelay _ => empty_set
    | CUnsc _ => empty_set
    | CEpi => empty_set
    | CStop => empty_set
    end.
  
  Definition make_ty_list (xs : list (string * SecTyV)) : SecTyV :=
    prodSecTyVlist (map snd xs).
  Hint Unfold make_ty_list.

  Definition make_pvar (κs : list string) (ℓs : list A) (αs : list string) (τs : list SecTyV) : VarT :=
    fold_right (fun p => update (fst p) (inr (snd p))) (fold_right (fun p => update (fst p) (inl (snd p))) ∅ (combine κs ℓs)) (combine αs τs).
  Hint Unfold make_pvar.

  Inductive make_parg : list (string * SecTy) -> VarT -> ArgT -> ArgT -> Prop :=
    MakePArgNil pvar parg: make_parg nil pvar parg parg
  | MakePArgCons x s τ ss pvar parg parg':
      ⟨s, (Build_PFrame pvar parg ∅)⟩ₛ ⇓ₛ τ ->
      make_parg ss pvar (update x τ parg) parg' ->
      make_parg ((x, s) :: ss) pvar parg parg'.
  Hint Constructors make_parg.

  Definition make_ploc (xs : set string) : LocT :=
    fold_right (fun x => update x (ASTyV NonSecTyV)) ∅ xs.
  Hint Unfold make_ploc.
  
  Definition make_mem (xs : list string) (vs : list V) (base: nat): option MemT :=
    let fix visit xs vs : option MemT :=
        match (xs, vs) with
          (nil, nil) => Some ∅
        | (x :: xs', v :: vs') =>
          match (visit xs' vs', δ x) with
            (Some m, Some nx) => Some (m [ Z.to_nat (nx + base) ↦ v ])
          | (_, _) => None
          end
        | (_, _) => None
        end
    in visit xs vs.
  Hint Unfold make_mem.
  
  Reserved Notation "cfg1 '-->' cfg2" (at level 80).

  Inductive Step: cfg -> cfg -> Prop :=
  | SSkip stk q ν: ⟨CSkip, stk, q, ν⟩ --> ⟨CStop, stk, q + 1, ν⟩
  | SLet x s e c stk fr q ν v τ n:
      ⟨s, pframe_of fr⟩ₛ ⇓ₛ τ ->
      ⟨e, fr⟩ₑ ⇓ₑ v ->
      δ x = Some n ->
      ⟨CLet x s e c, fr :: stk, q, ν⟩ -->
      ⟨CSeq c (CUnsc x), Build_Frame (upd_loc x τ (pframe_of fr)) (eframe_of fr [addr_of n fr ↦ v]) :: stk, q + 1, ν⟩
  | SIf1 c1 c2 e fr stk (n : nat) q ν:
      ⟨e, fr⟩ₑ ⇓ₑ VNum n ->
      n <> 0 ->
      ⟨CIf e c1 c2, fr :: stk, q, ν⟩ --> ⟨c1, fr :: stk, q + 1, ν⟩
  | SIf2 c1 c2 e fr stk q ν:
      ⟨e, fr⟩ₑ ⇓ₑ VNum 0 ->
      ⟨CIf e c1 c2, fr :: stk, q, ν⟩ --> ⟨c2, fr :: stk, q + 1, ν⟩
  | SWhile1 c e fr stk n q ν:
      ⟨e, fr⟩ₑ ⇓ₑ VNum n ->
      n <> 0 ->
      ⟨CWhile e c, fr :: stk, q, ν⟩ --> ⟨CSeq c (CWhile e c), fr :: stk, q + 1, ν⟩
  | SWhile2 c e fr stk q ν:
      ⟨e, fr⟩ₑ ⇓ₑ VNum 0 ->
      ⟨CWhile e c, fr :: stk, q, ν⟩ --> ⟨CStop, fr :: stk, q + 1, ν⟩
  | SSeq1 c1 c1' c2 stk stk' q q' ν ν':
      ⟨c1, stk, q, ν⟩ --> ⟨c1', stk', q', ν'⟩ ->
      c1' <> CStop ->
      ⟨CSeq c1 c2, stk, q, ν⟩ --> ⟨CSeq c1' c2, stk', q', ν'⟩
  | SSeq2 c1 c2 stk stk' q q' ν ν':
      ⟨c1, stk, q, ν⟩ --> ⟨CStop, stk', q', ν'⟩ ->
      ⟨CSeq c1 c2, stk, q, ν⟩ --> ⟨c2, stk', q', ν'⟩
  | SWrite e1 e2 stk1 stk2 q fr1 fr2 ν γ a v:
      hd_error (stk1 ++ fr1 :: stk2) = Some fr2 ->
      ⟨e1, fr2⟩ₑ ⇓ₑ VAddr a γ ->
      ⟨e2, fr2⟩ₑ ⇓ₑ v ->
      a ∈ fr1 ->
      version fr1 <= γ ->
      ⟨CWrite e1 e2, stk1 ++ fr1 :: stk2, q, ν⟩ --> ⟨CStop, stk1 ++ (fr1 [a ↦ v]) :: stk2, q + 1, ν⟩
  | SRead e fr a γ x stk q ν n (v : V):
      δ x = Some n ->
      ⟨e, fr⟩ₑ ⇓ₑ VAddr a γ ->
      (fr :: stk) ? a = Some v ->
      ⟨CRead x e, fr :: stk, q, ν⟩ --> ⟨CStop, (fr [addr_of n fr ↦ v]) :: stk, q + 1, ν⟩
  | SAt k e c fr stk q ν n:
      ⟨e, fr⟩ₑ ⇓ₑ VNum n ->
      ⟨CAt k e c, fr :: stk, q, ν⟩ --> ⟨CSeq c (CDelay n), fr :: stk, q + 1, ν⟩
  | SDelay n stk q ν:
      q <= n ->
      ⟨CDelay n, stk, q, ν⟩ --> ⟨CStop, stk, n + 1, ν⟩
  | SLabIf1 k1 k2 c1 c2 stk q ν ℓ1 ℓ2 fr:
      ⟨k1, pframe_of fr⟩ₖ ⇓ₖ ℓ1 ->
      ⟨k2, pframe_of fr⟩ₖ ⇓ₖ ℓ2 ->
      ℓ1 ⊑ ℓ2 ->
      ⟨CLabIf k1 k2 c1 c2, fr :: stk, q, ν⟩ --> ⟨c1, fr :: stk, q + 1, ν⟩
  | SLabIf2 k1 k2 c1 c2 stk q ν ℓ1 ℓ2 fr:
      ⟨k1, pframe_of fr⟩ₖ ⇓ₖ ℓ1 ->
      ⟨k2, pframe_of fr⟩ₖ ⇓ₖ ℓ2 ->
      ~ ℓ1 ⊑ ℓ2 ->
      ⟨CLabIf k1 k2 c1 c2, fr :: stk, q, ν⟩ --> ⟨c2, fr :: stk, q + 1, ν⟩
  | SMatch α pats fr pfr' stk τ q ν p c:
      fr ? α = Some (inr τ) ->
      find_match τ pats = Some (p, c) ->
      close p τ (pframe_of fr) = Some pfr' ->
      ⟨CMatch α pats, fr :: stk, q, ν⟩ --> ⟨c, Build_Frame pfr' (eframe_of fr) :: stk, q + 1, ν⟩
  | SFP x fr stk q ν n τ_arg τ_loc:
      δ x = Some n ->
      make_ty_list (values (parg_of (pframe_of fr))) = τ_arg ->
      make_ty_list (values (ploc_of (pframe_of fr))) = τ_loc ->
      ⟨CFP x, fr :: stk, q, ν⟩ -->
      ⟨CStop, fr [addr_of n fr ↦ ExTy τ_arg (ExTy τ_loc (VAddr (fp_of fr) ν))] :: stk, q + 1, ν⟩
  | SUnpTy α k x s e c fr τ τ1 n v2 stk q ν:
      ⟨e, fr⟩ₑ ⇓ₑ ExTy τ1 v2 ->
      ⟨s, pframe_of fr [α ↦ inr τ1]⟩ₛ ⇓ₛ τ ->
      δ x = Some n ->
      ⟨CUnpTy α k x s e c, fr :: stk, q, ν⟩ -->
      ⟨CSeq c (CUnsc x), Build_Frame (upd_loc x τ (pframe_of fr [α ↦ inr τ1])) (eframe_of fr [addr_of n fr ↦ v2]) :: stk, q + 1, ν⟩
  | SUnpLab κ k x s e c fr τ ℓ1 n v2 stk q ν:
      ⟨e, fr⟩ₑ ⇓ₑ ExLab ℓ1 v2 ->
      ⟨s, pframe_of fr [κ ↦ inl ℓ1]⟩ₛ ⇓ₛ τ ->
      δ x = Some n ->
      ⟨CUnpLab κ k x s e c, fr :: stk, q, ν⟩ -->
      ⟨CSeq c (CUnsc x), Build_Frame (upd_loc x τ (pframe_of fr [κ ↦ inl ℓ1])) (eframe_of fr [addr_of n fr ↦ v2]) :: stk, q + 1, ν⟩
  | SUnsc x fr stk q ν:
      ⟨CUnsc x, fr :: stk, q, ν⟩ --> ⟨CStop, Build_Frame (upd_loc x NonSecTyV (pframe_of fr)) (eframe_of fr) :: stk, q + 1, ν⟩
  | SCall f ks ss es κs αs ss' stk q ν c ℓs τs vs pvar' parg' ploc' xs τ_arg τ_loc m' pfr'' efr'' fr fr_k pc_k:
      F f = Some (κs, αs, ss', fr_k, pc_k, c) ->
      length ks = length ℓs ->
      length ss = length τs ->
      length es = length vs ->
      (forall i ℓ k, nth_error ks i = Some k /\ nth_error ℓs i = Some ℓ -> ⟨k, pframe_of fr⟩ₖ ⇓ₖ ℓ) ->
      (forall i τ s, nth_error ss i = Some s /\ nth_error τs i = Some τ -> ⟨s, pframe_of fr⟩ₛ ⇓ₛ τ) ->
      (forall i v e, nth_error es i = Some e /\ nth_error vs i = Some v -> ⟨e, fr⟩ₑ ⇓ₑ v) ->
      pvar' = make_pvar (map fst κs) ℓs (map fst αs) τs ->
      xs = vars c ->
      make_parg ss' pvar' ∅ parg' ->
      ploc' = make_ploc xs ->

      make_ty_list (values (parg_of (pframe_of fr))) = τ_arg ->
      make_ty_list (values (ploc_of (pframe_of fr))) = τ_loc ->
      make_mem (map fst ss') vs (S (sp_of fr) + length vs) = Some m' ->

      pfr'' = Build_PFrame pvar' parg' ploc' ->
      efr'' = Build_EFrame (S (sp_of fr) + length vs, length xs)
                           (m' [sp_of fr + length vs ↦
                                  ExTy τ_arg (ExTy τ_loc (VAddr (fp_of fr) ν)) ])
                           (version fr) ->
      
      ⟨CCall f ks ss es, fr :: stk, q, ν⟩ -->
      ⟨CSeq c CEpi, (Build_Frame pfr'' efr'') :: fr :: stk, q + 1, ν + 1⟩
  | SEpi fr stk q ν: ⟨CEpi, fr :: stk, q, ν⟩ --> ⟨CStop, stk, q + 1, ν⟩
  where "cfg1 '-->' cfg2" := (Step cfg1 cfg2).
  Hint Constructors Step.
  
  Definition initial_stk (c : Cmd) : Stk :=
    let xs := vars c
    in Build_Frame (Build_PFrame ∅ ∅ (make_ploc xs))
                   (Build_EFrame (1, length xs)
                                 (∅ [0 ↦ ExTy NilTyV (ExTy NilTyV (VAddr 0 0))]) 0) :: nil.
  Hint Unfold initial_stk.
  
  Reserved Notation "cfg1 '-->[' n ']' cfg2" (at level 80).
  Inductive step_many: cfg -> cfg -> nat -> Prop :=
  | StepMany0 C: C -->[0] C
  | StepManyS C C' C'' n:
      C --> C' ->
      C' -->[n] C'' ->
      C -->[S n] C''
  where "cfg1 '-->[' n ']' cfg2" := (step_many cfg1 cfg2 n).
  Hint Constructors step_many.
  
  Notation "cfg1 '-->*' cfg2" := (exists n, cfg1 -->[n] cfg2) (at level 80).
End Sem.

Notation "'⟨' e ',' fr '⟩ₑ'" := (make_ecfg e fr).
Notation "'⟨' s ',' pfr '⟩ₛ'" := (make_scfg s pfr).
Notation "'⟨' a ',' pfr '⟩ₐ'" := (make_acfg a pfr).
Notation "'⟨' t ',' pfr '⟩ₜ'" := (make_tcfg t pfr).
Notation "'⟨' k ',' pfr '⟩ₖ'" := (make_kcfg k pfr).
Notation "kcfg '⇓ₖ' ℓ" := (EvalLab kcfg ℓ) (at level 80).
Notation "tcfg '⇓ₜ' π" := (EvalTy tcfg π) (at level 80).
Notation "scfg '⇓ₛ' τ" := (EvalSecTy scfg τ) (at level 80).
Notation "scfg '⇓ₐ' π" := (EvalAtomSecTy scfg π) (at level 80).
Notation "ecfg '⇓ₑ' v" := (EvalExpr ecfg v) (at level 80).
Notation "'⟨' c ',' stk ',' q ',' ν '⟩'" := (make_cfg c stk q ν).
Notation "cfg1 '-->' cfg2" := (Step cfg1 cfg2) (at level 80).
Notation "cfg1 '-->[' n ']' cfg2" := (step_many cfg1 cfg2 n) (at level 80).
Notation "cfg1 '-->*' cfg2" := (exists n, cfg1 -->[n] cfg2) (at level 80).

  Ltac solve_mapsto :=
    repeat (repeat autounfold with *; cbn;
            match goal with
              [ |- _ [_ ↦ ?v ] ? _ = Some _ ] =>
              rewrite -> lookup_update_eq; reflexivity
            | [ |- _ [_ ↦ ?v ] ? _ = Some _ ] =>
              rewrite -> lookup_update_neq by solve[lia]
            end).

  Ltac simpl_mapsto :=
    repeat (repeat autounfold with *; cbn;
            match goal with
              [ |- context[_ [_ ↦ ?v ] ? _] ] =>
              rewrite -> lookup_update_eq
            | [ |- context[_ [_ ↦ ?v ] ? _] ] =>
              rewrite -> lookup_update_neq by solve[lia]
            end).

  Ltac solve_in_range := 
    (repeat autounfold with *; cbn; lia).
  
  Ltac eval_var :=
    (repeat autounfold with *; cbn; eapply EVar;
     [eassumption | solve_mapsto]).

  Ltac eval_addrof :=
    repeat autounfold with *; cbn; eapply EAddrOf; [eassumption].

  Ltac eval_expr :=
    repeat (repeat autounfold with *; cbn; match goal with
                     [ |- ⟨BinOp _ _ _, _⟩ₑ ⇓ₑ _ ] => eapply EBinOp
                   | [ |- ⟨Var _, _⟩ₑ ⇓ₑ _] => eval_var
                   | [ |- ⟨AddrOf _, _⟩ₑ ⇓ₑ _] => eval_addrof
                   | [ |- ⟨Num ?n, _⟩ₑ ⇓ₑ _] => constructor
                   end).

  Ltac step_write :=
    match goal with
      [ |- ⟨_ *= _, ?stk, _, _⟩ --> _] =>
      rewrite <- (app_nil_l stk)
    end; eapply SWrite; [reflexivity | eval_expr | eval_expr | solve_in_range | solve_in_range].

  Ltac step_let :=
    eapply SLet; [(constructor; repeat constructor) | eval_expr | eassumption].
  
  
  Ltac step_while1 :=
    eapply SWhile1; [ eval_var | lia ].

  Ltac step_while2 :=
      eapply SWhile2; [ eval_var ].

  Ltac step_while := step_while1 || step_while2.

  Ltac step_match :=
    eapply SMatch; [cbn; solve_mapsto | cbn; reflexivity | cbn; reflexivity].

  Ltac step_unpack_ty :=
    eapply SUnpTy; [eval_expr | constructor; repeat constructor | eassumption].
  
  Ltac step_seq :=
    match goal with
      [ |- ⟨ CSkip ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2
    | [ |- ⟨ (CLet _ _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CIf _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CWhile _ _) ;; _ , _, _, _⟩ --> _ ] =>
      solve[eapply SSeq1; step_while] || solve[eapply SSeq2; step_while]
    | [ |- ⟨ (_ ;; _) ;; _ , _, _, _⟩ --> _ ] =>
      eapply SSeq1
    | [ |- ⟨ (CWrite _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2
    | [ |- ⟨ (CRead _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2
    | [ |- ⟨ (CAt _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CLabIf _ _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CMatch _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CFP _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2
    | [ |- ⟨ (CCall _ _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CUnpTy _ _ _ _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CUnpLab _ _ _ _ _ _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq1
    | [ |- ⟨ (CDelay _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2
    | [ |- ⟨ (CUnsc _) ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2
    | [ |- ⟨ CEpi ;; _ , _, _, _⟩ --> _ ] => eapply SSeq2   
    end.