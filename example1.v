Require Import Autosubst.Autosubst.
Require Import Zee.lattice Zee.lang Zee.dec Zee.vals Zee.frame Zee.maplike Zee.sem Zee.typesystem Coq.Strings.String.
Require Import Arith List Coq.Program.Basics Coq.Lists.ListSet Lia Coq.ZArith.BinInt.
Require Import Coq.Classes.RelationClasses.

Section Example1.
  Context {A : Set} {BinOpS : Set} `{lattice A}.
  Context {MINUS MULT : BinOpS}.
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
  Context {type_binop: BinOpS -> SecTy -> SecTy -> SecTy -> Prop}.
  Context {VarT ArgT LocT MemT : Type}
          {H_var_finmaplike: FinMapLike VarT string (A + SecTyV)}
          {H_arg_finmaplike: FinMapLike ArgT string SecTyV}
          {H_loc_finmaplike: FinMapLike LocT string SecTyV}
          {H_mem_maplike: MapLike MemT nat V}.
  Definition Frame := @Frame A VarT ArgT LocT MemT _ _ _ _.
  Definition PFrame := @PFrame A VarT ArgT LocT _ _ _.
  Definition EFrame := @EFrame A MemT _.
  
  Notation "'〚' o '〛'" := (eval_binop o).
  Notation "o ':' s1 ',' s2 '⤇' s" := (type_binop o s1 s2 s) (at level 70, s at next level).
 
  Definition Var := @Var A BinOpS.
  Definition Num := @Num A BinOpS.
  Coercion Var: string >-> lang.Expr.
  Coercion Num: nat >-> lang.Expr.
  Coercion STy: lang.Ty >-> Funclass.
  Coercion eval_binop : BinOpS >-> Funclass.
    
  Definition factorial : Cmd :=
    LET "fac_var0" AS (IntTy ⊥) ::= 1
    IN LET "fac_var1" AS (IntTy ⊥) ::= "fac_arg0"
       IN WHILE "fac_var1" DO
            &("fac_var0") *= BinOp MULT "fac_var0" "fac_var1" ;;
            &("fac_var1") *= BinOp MINUS "fac_var1" 1
          END
       ENDLET;;
       Var "fac_arg1" *= Var "fac_var0"
    ENDLET.
    Hint Unfold factorial.
    
    Definition program : Cmd :=
      LET "program_var0" AS (IntTy ⊥) ::= Num 0
      IN CALL "fac" nil nil (Num 3 :: &("program_var0") :: nil);;
         LET "program_var1" AS (IntTy ⊥) ::= "program_var0"
         IN SKIP ENDLET
      ENDLET.
    Hint Unfold program.

    Definition step_many := @step_many A BinOpS _ δ F eval_binop _ _ _ _ _ _ _ _.
    Notation "cfg1 '-->[' n ']' cfg2" := (step_many cfg1 cfg2 n) (at level 80).
    Notation "cfg1 '-->*' cfg2" := (exists n, cfg1 -->[n] cfg2) (at level 80).

    Definition wt := @wt A BinOpS _ F type_binop.
    Notation "'[' Γ ',' Π ',' ϕ ',' pc ',' fr ']' '⊢' c" := (wt Γ Π ϕ pc fr c) (at level 70, c at next level).

    Lemma fac_is_wt:
      (forall k1 k2 o, o : (IntTy k1), (IntTy k2) ⤇ (ASecTy (IntTy (k1 ⊔ k2)))) ->
      [∅["fac_arg0" ↦ ASecTy (IntTy ⊥)]
        ["fac_arg1" ↦ ASecTy (STy (ε @ (ASecTy (IntTy ⊥))) ⊥)],
       ∅, nil, ⊥, ⊥] ⊢ factorial.
    Proof.
      intros.
      unfold factorial.
      eapply WtLet.
      - constructor.
      - constructor; repeat constructor.
      - constructor.
        constructor.
        rewrite -> idem_join.
        reflexivity.
      - rewrite -> idem_join.
        reflexivity.
      - eapply WtSeq.
        + eapply WtLet.
          * constructor.
            reflexivity.
          * constructor; repeat constructor.
          * constructor.
            constructor.
            rewrite -> idem_join.
            reflexivity.
          * rewrite -> idem_join.
            reflexivity.
          * eapply WtWhile.
            -- constructor.
               reflexivity.
            -- eapply WtSeq.
               ++ eapply WtWrite.
                  ** constructor.
                     reflexivity.
                  ** eapply wt_binop.
                     {
                       constructor.
                       reflexivity.
                     }
                     {
                       constructor.
                       reflexivity.
                     }
                     {
                       eauto.
                     }
                  ** constructor.
                     constructor.
                     do 2 rewrite -> idem_join.
                     reflexivity.
               ++ eapply WtWrite.
                  ** constructor.
                     reflexivity.
                  ** eapply wt_binop.
                     {
                       constructor.
                       reflexivity.
                     }
                     {
                       constructor.
                     }
                     {
                       eauto.
                     }
                  ** constructor.
                     constructor.
                     do 2 rewrite -> idem_join.
                     reflexivity.
        + eapply WtWrite.
          * constructor.
            reflexivity.
          * constructor.
            reflexivity.
          * constructor.
            constructor.
            rewrite -> idem_join.
            reflexivity.
    Qed.
    
    Lemma program_is_wt:
      F "fac" = Some (nil, nil, ("fac_arg0", ASecTy (IntTy ⊥)) :: ("fac_arg1", ASecTy (STy (ε @ (ASecTy (IntTy ⊥))) ⊥)) :: nil, ⊥, ⊥, factorial) ->
      [∅, ∅, nil, ⊥, ⊥] ⊢ program.
    Proof.
      intros.
      unfold program.
      eapply WtLet.
      - constructor.
      - constructor. constructor; constructor.
      - constructor.
        constructor.
        rewrite -> idem_join.
        reflexivity.
      - rewrite -> idem_join.
        reflexivity.
      - eapply WtSeq.
        + eapply WtCall.
          * eassumption.
          * reflexivity.
          * reflexivity.
          * reflexivity.
          * intros.
            eapply nth_error_In in H1.
            firstorder.
          * intros.
            eapply nth_error_In in H1.
            firstorder.
          * intros.
            destruct i.
            {
              cbn in * |-.
              inversion H1; subst; clear H1.
              inversion H2; subst; clear H2.
              constructor.
            }
            destruct i.
            {
              cbn in * |-.
              inversion H1; subst; clear H1.
              inversion H2; subst; clear H2.
              constructor.
              reflexivity.
            }
            cbn in * |-.
            eapply nth_error_In in H1.
            firstorder.
          * split.
            -- cbn.
               reflexivity.
            -- cbn.
               reflexivity.
          * cbn.
            reflexivity.
        + eapply WtLet.
          * constructor.
            reflexivity.
          * constructor; repeat constructor.
          * constructor.
            constructor.
            rewrite -> idem_join.
            reflexivity.
          * rewrite -> idem_join.
            reflexivity.
          * eapply WtSkip.
    Qed.

    Goal
      δ "fac_var0" = Some 0%Z ->
      δ "fac_var1" = Some 1%Z ->
      δ "fac_arg0" = Some (Z.neg 3)%Z ->
      δ "fac_arg1" = Some (Z.neg 2)%Z ->
      δ "program_var0" = Some 0%Z ->
      δ "program_var1" = Some 1%Z ->
      (forall n m, 〚 MINUS 〛 n m =
              match (n, m) with
                (VNum n, VNum m) => VNum (n - m)
              | _ => VNum 0
              end) ->
      (forall n m, 〚 MULT 〛 n m =
              match (n, m) with
                (VNum n, VNum m) => VNum (n * m)
              | _ => VNum 0
              end) ->
      F "fac" = Some (nil, nil, ("fac_arg0", ASecTy (IntTy ⊥)) :: ("fac_arg1", ASecTy (STy (ε @ (ASecTy (IntTy ⊥))) ⊥)) :: nil, ⊥, ⊥, factorial) ->
      exists stk q,
        ⟨program, initial_stk program, 0, 0⟩ -->* ⟨CStop, stk, q, 1⟩ /\
        stk ? (1 + fp_of (initial_stk program)) = Some (VNum 6).
    Proof.
      intros.
      do 2 eexists.
      split.
      {
        eexists.
        unfold program.
        cbn in *.
        eapply StepManyS.
        - step_let.
        - cbn. eapply StepManyS.
          + step_seq.
            step_seq.
            eapply SCall.
            * eassumption.
            * instantiate (1 := nil).
              reflexivity.
            * instantiate (1 := nil).
              reflexivity.
            * instantiate (1 := VNum 3 :: _ :: nil).
              reflexivity.
            * cbn in *.
              intros i ℓ k [? ?].
              eapply nth_error_In in H9.
              firstorder.
            * cbn in *.
              intros i τ s [? ?].
              eapply nth_error_In in H9.
              firstorder.
            * cbn in *.
              intros i v e [? ?].
              destruct i.
              -- cbn in *.
                 inversion H9; inversion H10; subst; clear H9 H10.
                 constructor.
              -- destruct i.
                 ++ cbn in *.
                    inversion H9; inversion H10; subst; clear H9 H10.
                    constructor.
                    ** eassumption.
                 ++ cbn in *.
                    eapply nth_error_In in H9.
                    firstorder.
            * cbn. reflexivity.
            * cbn. reflexivity.
            * eapply MakePArgCons.
              -- constructor.
                 constructor; constructor.
              -- eapply MakePArgCons.
                 ++ constructor.
                    constructor; repeat constructor.
                 ++ constructor.
            * cbn. reflexivity.
            * cbn. reflexivity.
            * cbn. reflexivity.
            * cbn.
              rewrite -> H3.
              rewrite -> H2.
              reflexivity.
            * reflexivity.
            * cbn. reflexivity.
            * easy.
            * easy.
          + cbn.
            eapply StepManyS.
            * unfold factorial.
              repeat step_seq; try easy.
              step_let.
              easy.
            * eapply StepManyS.
              repeat step_seq; try easy.
              step_let.
              easy.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              eapply SSeq1.
              step_while.
              all: try (easy).
              eapply StepManyS.
              repeat step_seq; try easy.
              step_write.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              step_write.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              eapply SSeq1.
              repeat rewrite -> H6, H7. step_while.
              all: try (easy).
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              step_write.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              step_write.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              eapply SSeq1.
              repeat rewrite -> H6, H7. step_while.
              all: try (easy).
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              step_write.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              step_write.
              cbn. eapply StepManyS. 
              repeat step_seq; try easy.
              repeat rewrite -> H6, H7.
              eapply SSeq2.
              step_while.
              easy.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              constructor.
              cbn. eapply StepManyS.
              repeat step_seq; try easy.
              repeat rewrite -> (values_add _ _ _ _).
              repeat rewrite -> values_empty.
              match goal with
                [ |- ⟨_, ?fr1 :: ?fr2 :: ?stk, _, _⟩ --> _] =>
                replace (fr1 :: fr2 :: stk) with ((fr1 :: nil) ++ (fr2 :: stk))
                  by reflexivity
              end; eapply SWrite.
              -- simpl. reflexivity.
              -- eval_var.
              -- eval_var.
              -- cbn. lia.
              -- cbn. lia.
              -- eapply StepManyS.
                 repeat step_seq; try easy.
                 constructor.
                 cbn. eapply StepManyS.
                 repeat step_seq; try easy.
                 constructor.
                 cbn. eapply StepManyS.
                 repeat step_seq; try easy.
                 step_let.
                 easy.
                 cbn. eapply StepManyS.
                 repeat step_seq; try easy.
                 constructor.
                 eapply StepManyS.
                 repeat step_seq; try easy.
                 constructor.
                 cbn. eapply StepManyS.
                 constructor.
                 eapply StepMany0.
      }
      {
        simpl_mapsto.
        reflexivity.
      }
    Qed.

End Example1.