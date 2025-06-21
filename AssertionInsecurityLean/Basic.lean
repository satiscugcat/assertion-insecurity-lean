import Mathlib

inductive TermVar
| cons : Nat -> TermVar
deriving DecidableEq

inductive KeyVar
| cons : Nat  -> KeyVar
deriving DecidableEq

inductive Name
| cons : Nat -> Name
deriving DecidableEq

inductive Var
| term (t: TermVar) 
| key (k:KeyVar)
deriving DecidableEq


inductive Key: Type
| priv (k: Name)
| pub (k: Name)
| var (v: KeyVar)
deriving DecidableEq

inductive Term: Type
| var (v: TermVar)
| name (m: Name)
| key (k: Key)
| pair (t1 t2: Term)
| enc (t: Term) (k: Key)
deriving DecidableEq

abbrev TermSet := Set Term
def var_to_term (v: Var) : Term :=
  match v with
  | Var.term v => Term.var v
  | Var.key v => Term.key (Key.var v)
 


def FVSetTerm : Term -> Set Var
| Term.var v => {Var.term v}
| Term.name _ => ∅ 
| Term.key (Key.var v) => {Var.key v}
| Term.key _ => ∅
| Term.pair t1 t2 =>  FVSetTerm t1 ∪ FVSetTerm t2
| Term.enc t' k => (FVSetTerm t') ∪
                           match k with 
                             | Key.var v => {Var.key v} 
                             | _ => ∅


      
inductive dy : TermSet -> Term -> Type
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (Term.key (Key.priv k)) ) : dy X (Term.key (Key.pub k))
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (Term.pair t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.priv k))) : dy X (Term.enc t (Key.priv k))
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dy X (Term.enc t (Key.pub k))


inductive dyProperSubProof : ∀ {X₁ X₂ t₁ t₂}, dy X₁ t₁ -> dy X₂ t₂ -> Prop
| pk {X: TermSet} {k: Name} (kH: dy X (Term.key (Key.priv k))) : dyProperSubProof kH (dy.pk kH)                                                       
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dyProperSubProof splitH (dy.splitL splitH)
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dyProperSubProof splitH (dy.splitR splitH)
| pair_left {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dyProperSubProof tH (dy.pair tH uH)
| pair_right {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dyProperSubProof uH (dy.pair tH uH)
                                                               
| sdec_enc {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof encH (dy.sdec encH kH)
| sdec_key {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof kH (dy.sdec encH kH)

| senc_term {X: TermSet} {t: Term} {k: Name} (tH: dy X t) {kH: dy X (Term.key (Key.priv k))} : dyProperSubProof tH (dy.senc tH kH)
| senc_key {X: TermSet} {t: Term} {k: Name} {tH: dy X t} (kH: dy X (Term.key (Key.priv k))) : dyProperSubProof kH (dy.senc tH kH)

| adec_enc {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof encH (dy.adec encH kH)
| adec_key {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof kH (dy.adec encH kH)                                                                                     
| aenc_term {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dyProperSubProof tH (dy.aenc tH kH)
| aenc_key {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dyProperSubProof kH (dy.aenc tH kH)

| trans_pk {X: TermSet} {k: Name} {kH: dy X (Term.key (Key.priv k))} {X' tp} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.pk kH)                                                       
| trans_splitL {X: TermSet} {t1 t2: Term} {splitH: dy X (Term.pair t1 t2)} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p splitH) : dyProperSubProof p (dy.splitL splitH)
| trans_splitR {X: TermSet} {t1 t2: Term} {splitH: dy X (Term.pair t1 t2)} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p splitH): dyProperSubProof p (dy.splitR splitH)
| trans_pair_left {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p tH): dyProperSubProof p (dy.pair tH uH)
| trans_pair_right {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p uH): dyProperSubProof p (dy.pair tH uH)
                                                               
| trans_sdec_enc {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.priv k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p encH): dyProperSubProof p (dy.sdec encH kH)
| trans_sdec_key {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.priv k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.sdec encH kH)

| trans_senc_term {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p tH): dyProperSubProof p (dy.senc tH kH)
| trans_senc_key {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH) : dyProperSubProof p (dy.senc tH kH)

| trans_adec_enc {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.pub k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p encH): dyProperSubProof p (dy.adec encH kH)
| trans_adec_key {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.pub k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.adec encH kH)                                                                                     
| trans_aenc_term {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p tH) : dyProperSubProof p (dy.aenc tH kH)
| trans_aenc_key {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.aenc tH kH)

theorem dySubProofTrans : ∀ {X₁ t₁ X₂ t₂ X₃ t₃} {p₁: dy X₁ t₁} {p₂: dy X₂ t₂} {p₃: dy X₃ t₃}, dyProperSubProof p₁ p₂ -> dyProperSubProof p₂ p₃ -> dyProperSubProof p₁ p₃ :=
  by
    intros _ _ _ _ _ _ p₁ p₂ p₃
    intros sub₁ sub₂
    induction sub₂ with
    | pk kH =>
      constructor
      exact sub₁
    | splitL splitH =>
      apply dyProperSubProof.trans_splitL
      exact sub₁
    | splitR splitH =>
      apply dyProperSubProof.trans_splitR
      exact sub₁
    | pair_left tH uH => 
      apply dyProperSubProof.trans_pair_left
      exact sub₁
    | pair_right =>
      apply dyProperSubProof.trans_pair_right
      exact sub₁
    | sdec_enc =>
      apply dyProperSubProof.trans_sdec_enc
      exact sub₁
    | sdec_key =>
      apply dyProperSubProof.trans_sdec_key
      exact sub₁
    | adec_enc =>
      apply dyProperSubProof.trans_adec_enc
      exact sub₁
    | adec_key =>
      apply dyProperSubProof.trans_adec_key
      exact sub₁
    | senc_term =>
      constructor
      exact sub₁
    | senc_key =>
      apply dyProperSubProof.trans_senc_key
      exact sub₁
    | aenc_term =>
      constructor
      exact sub₁
    | aenc_key =>
      apply dyProperSubProof.trans_aenc_key
      exact sub₁
    
    | trans_pk sub sub_ih =>
      apply dyProperSubProof.trans_pk
      apply sub_ih
      exact sub₁

    | trans_splitL sub sub_ih =>
      apply dyProperSubProof.trans_splitL
      apply sub_ih
      exact sub₁
    | trans_splitR sub sub_ih =>
      apply dyProperSubProof.trans_splitR
      apply sub_ih
      exact sub₁
    | trans_pair_left sub sub_ih => 
      apply dyProperSubProof.trans_pair_left
      apply sub_ih
      exact sub₁
    | trans_pair_right sub sub_ih =>
      apply dyProperSubProof.trans_pair_right
      apply sub_ih
      exact sub₁
    | trans_sdec_enc sub sub_ih =>
      apply dyProperSubProof.trans_sdec_enc
      apply sub_ih
      exact sub₁
    | trans_sdec_key sub sub_ih =>
      apply dyProperSubProof.trans_sdec_key
      apply sub_ih
      exact sub₁
    | trans_adec_enc sub sub_ih =>
      apply dyProperSubProof.trans_adec_enc
      apply sub_ih
      exact sub₁
    | trans_adec_key sub sub_ih =>
      apply dyProperSubProof.trans_adec_key
      apply sub_ih
      exact sub₁
    | trans_senc_term sub sub_ih =>
      constructor
      apply sub_ih
      exact sub₁
    | trans_senc_key sub sub_ih =>
      apply dyProperSubProof.trans_senc_key
      apply sub_ih
      exact sub₁
    | trans_aenc_term sub sub_ih =>
      constructor
      apply sub_ih
      exact sub₁
    | trans_aenc_key sub sub_ih  =>
      apply dyProperSubProof.trans_aenc_key
      apply sub_ih
      exact sub₁
 
    
      
    
theorem dyStrongInduction : ∀ {P: ∀ {X t}, dy X t → Prop}, 
        (∀ {X} {t} (p: dy X t), ( ∀ {X'} {t'} (p': dy X' t'), dyProperSubProof p' p → P p' ) → P p) → 
        ∀ {X t} (p: dy X t), P p :=
        by
          intros P iH
          have Q : ∀ {X t} (p: dy X t), P p ∧ ∀ {X' t'} (p': dy X' t'), dyProperSubProof p' p → P p'
          {
            intros X t p
            induction p with
            | ax =>
              apply And.intro
              {
                apply iH
                intros _ _ _ a
                cases a
              }
              intros _ _ p' sub
              cases sub
            | pk kH kH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | pk => 
                  apply And.left kH_ih
                | trans_pk sub =>
                  apply And.right kH_ih
                  exact sub
              }
              {
                intros _ _ p' sub
                cases sub with
                | pk =>
                  apply And.left kH_ih
                
                | trans_pk sub =>
                  apply And.right kH_ih
                  exact sub
              }
            | splitL splitH splitH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | splitL => exact And.left splitH_ih
                | trans_splitL sub => 
                  apply And.right splitH_ih
                  exact sub
              }
              {
                
                intros X' t' p' sub
                cases sub with
                | splitL => exact And.left splitH_ih
                | trans_splitL sub => 
                  apply And.right splitH_ih
                  exact sub
              }
            | splitR splitH splitH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | splitR => exact And.left splitH_ih
                | trans_splitR sub => 
                  apply And.right splitH_ih
                  exact sub
              }
              {
                
                intros X' t' p' sub
                cases sub with
                | splitR => exact And.left splitH_ih
                | trans_splitR sub => 
                  apply And.right splitH_ih
                  exact sub
              }
            | pair tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | pair_left => exact And.left tH_ih
                | trans_pair_left sub => 
                  apply And.right tH_ih
                  exact sub
                | pair_right => exact And.left uH_ih
                | trans_pair_right sub => 
                  apply And.right uH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | pair_left => exact And.left tH_ih
                | trans_pair_left sub => 
                  apply And.right tH_ih
                  exact sub
                | pair_right => exact And.left uH_ih
                | trans_pair_right sub => 
                  apply And.right uH_ih
                  exact sub
              }

            | sdec tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | sdec_key => exact And.left uH_ih
                | trans_sdec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | sdec_enc => exact And.left tH_ih
                | trans_sdec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | sdec_key => exact And.left uH_ih
                | trans_sdec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | sdec_enc => exact And.left tH_ih
                | trans_sdec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }

            | senc tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | senc_key => exact And.left uH_ih
                | trans_senc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | senc_term => exact And.left tH_ih
                | trans_senc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | senc_key => exact And.left uH_ih
                | trans_senc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | senc_term => exact And.left tH_ih
                | trans_senc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }

              | adec tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | adec_key => exact And.left uH_ih
                | trans_adec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | adec_enc => exact And.left tH_ih
                | trans_adec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | adec_key => exact And.left uH_ih
                | trans_adec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | adec_enc => exact And.left tH_ih
                | trans_adec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }

            | aenc tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | aenc_key => exact And.left uH_ih
                | trans_aenc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | aenc_term => exact And.left tH_ih
                | trans_aenc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | aenc_key => exact And.left uH_ih
                | trans_aenc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | aenc_term => exact And.left tH_ih
                | trans_aenc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }
          
          }
          intros X t p
          apply And.left (Q p)

noncomputable def TermMonotonicity (X Y: TermSet) : ∀   (t: Term), (dy X t) → (X ⊆ Y) →  (dy Y t) :=
  by
    intros t dyxt subset
    induction dyxt with
    | ax inH => exact dy.ax (subset inH)
    | pk _ kH_ih => exact dy.pk kH_ih  
    | splitL _ splitH_iH => exact dy.splitL splitH_iH
    | splitR _ splitH_iH => exact dy.splitR splitH_iH
    | pair _ _ tH_iH uH_iH => exact dy.pair tH_iH uH_iH
    | sdec _ _ encH_iH kH_iH => exact dy.sdec encH_iH kH_iH
    | senc _ _ tH_ih kH_iH => exact dy.senc tH_ih kH_iH
    | adec _ _ encH_iH kH_iH => exact dy.adec encH_iH kH_iH
    | aenc _ _ tH_ih kH_iH =>  exact dy.aenc tH_ih kH_iH


inductive NormalProof: ∀ {X: TermSet} {t: Term}, dy X t → Prop
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : NormalProof (dy.ax inH)
| pk {X: TermSet} {k: Name} {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) 
     : NormalProof (dy.pk kH)
| pair {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} 
     (tN: NormalProof tH) (uN: NormalProof uH)
     : NormalProof (dy.pair tH uH)
| senc {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} (tN: NormalProof tH) (kN: NormalProof kH): NormalProof (dy.senc tH kH)
| aenc {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} (tN: NormalProof tH) (kN: NormalProof kH): NormalProof (dy.aenc tH kH)

| splitL_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair (Term.pair t₁ t₂) t₃)} (pN: NormalProof pH): NormalProof (dy.splitL (dy.splitL pH))
| splitL_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair t₃ (Term.pair t₁ t₂))} (pN: NormalProof pH): NormalProof (dy.splitL (dy.splitR pH))
| splitL_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₁ t₂) (Key.priv k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitL (dy.sdec pH kH))
| splitL_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₁ t₂) (Key.pub k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitL (dy.adec pH kH))

| splitR_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair (Term.pair t₂ t₁) t₃)} (pN: NormalProof pH): NormalProof (dy.splitR (dy.splitL pH))
| splitR_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair t₃ (Term.pair t₂ t₁))} (pN: NormalProof pH): NormalProof (dy.splitR (dy.splitR pH))
| splitR_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₂ t₁) (Key.priv k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitR (dy.sdec pH kH))
| splitR_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₂ t₁) (Key.pub k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitR (dy.adec pH kH))

| sdec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair (Term.enc t₁ (Key.priv k)) t₂)} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.sdec (dy.splitL pH) kH)
| sdec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair t₂ (Term.enc t₁ (Key.priv k)))} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.sdec (dy.splitR pH) kH)
| sdec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.priv k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.sdec (dy.sdec pH k₂H) k₁H)
| sdec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.pub k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.sdec (dy.adec pH k₂H) k₁H)

| adec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair (Term.enc t₁ (Key.pub k)) t₂)} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.adec (dy.splitL pH) kH)
| adec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair t₂ (Term.enc t₁ (Key.pub k)))} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.adec (dy.splitR pH) kH)
| adec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.priv k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.adec (dy.sdec pH k₂H) k₁H)
| adec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.pub k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.adec (dy.adec pH k₂H) k₁H)




@[simp]
def isNormal {X: TermSet} {t: Term} (proof: dy X t): Bool :=
    match proof with
    | dy.ax _ =>  true
    | dy.pk kH =>  (isNormal kH)
    | dy.splitL splitH =>            
                    match splitH with
                    | dy.ax _ =>  true
                    | dy.splitL splitH =>  isNormal splitH 
                    | dy.splitR splitH =>  isNormal splitH
                    | dy.sdec kH encH =>  isNormal kH && isNormal encH
                    | dy.adec kH encH =>  isNormal kH && isNormal encH
                    | dy.pair _ _ =>  false
    | dy.splitR splitH =>            
                    match splitH with
                    | dy.ax _ =>  true
                    | dy.splitL splitH =>  isNormal splitH 
                    | dy.splitR splitH =>  isNormal splitH
                    | dy.sdec kH encH =>  isNormal kH && isNormal encH
                    | dy.adec kH encH =>  isNormal kH && isNormal encH
                    | dy.pair _ _ =>  false
    | dy.pair tH uH =>  isNormal tH && isNormal uH
    | dy.senc tH kH =>  isNormal tH && isNormal kH
    | dy.aenc tH kH =>  isNormal tH && isNormal kH
    | dy.sdec encH kH => isNormal kH &&
                      match encH with
                      | dy.ax _ =>  true
                      | dy.splitL splitH =>  isNormal splitH 
                      | dy.splitR splitH =>  isNormal splitH
                      | dy.sdec kH encH =>  isNormal kH && isNormal encH
                      | dy.adec kH encH =>  isNormal kH && isNormal encH
                      | dy.senc _ _ =>  false
    | dy.adec encH kH => isNormal kH &&
                      match encH with
                      | dy.ax _ =>  true
                      | dy.splitL splitH =>  isNormal splitH 
                      | dy.splitR splitH =>  isNormal splitH
                      | dy.sdec kH encH =>  isNormal kH && isNormal encH
                      | dy.adec kH encH =>  isNormal kH && isNormal encH
                      | dy.aenc _ _ =>  false
@[simp]
def dyProofMeasure {X: TermSet} {t: Term} (proof: dy X t): Nat := 
      1 +
      match proof with
      | dy.ax _ =>  1
      | dy.pk kH =>  dyProofMeasure kH
      | dy.splitL splitH =>  dyProofMeasure splitH
      | dy.splitR splitH =>  dyProofMeasure splitH
      | dy.pair tH uH =>  dyProofMeasure tH + dyProofMeasure uH
      | dy.senc tH kH =>   dyProofMeasure tH + dyProofMeasure kH
      | dy.aenc tH kH =>   dyProofMeasure tH + dyProofMeasure kH
      | dy.sdec encH kH =>  dyProofMeasure encH + dyProofMeasure kH
      | dy.adec encH kH =>  dyProofMeasure encH + dyProofMeasure kH

@[simp]
def dyProofRewrite {X: TermSet} {t: Term} (proof: dy X t): dy X t :=
  match proof with
  | dy.splitL splitH =>
              match splitH with
              | dy.pair uH _ => uH
              | _ => proof
  | dy.splitR splitH =>
              match splitH with
              | dy.pair _ tH => tH
              | _ => proof
  | dy.sdec encH _ =>
              match encH with
              | dy.senc  tH _ => tH
              | _ => proof
  | dy.adec encH _ =>
              match encH with
              | dy.aenc  tH _ => tH
              | _ => proof
  | _ => proof

inductive RewriteBigStep: ∀ {X: TermSet} {t: Term}, dy X t -> dy X t -> Prop
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : RewriteBigStep (dy.ax inH) (dy.ax inH)
| pk {X: TermSet} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') 
     : RewriteBigStep (dy.pk kH) (dy.pk kH')
| pair {X: TermSet} {t₁ t₂: Term} {tH tH': dy X t₁} {uH uH': dy X t₂} 
     (tN: RewriteBigStep tH tH') (uN: RewriteBigStep uH uH')
     : RewriteBigStep (dy.pair tH uH) (dy.pair tH' uH')
| senc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {kH kH': dy X (Term.key (Key.priv k))} (tN: RewriteBigStep tH tH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.senc tH kH) (dy.senc tH' kH')
| aenc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {kH kH': dy X (Term.key (Key.pub k))} (tN: RewriteBigStep tH tH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.aenc tH kH) (dy.aenc tH' kH')

| splitL_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH pH' : dy X (Term.pair (Term.pair t₁ t₂) t₃)} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitL (dy.splitL pH)) (dy.splitL (dy.splitL pH'))
| splitL_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH pH': dy X (Term.pair t₃ (Term.pair t₁ t₂))} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitL (dy.splitR pH)) (dy.splitL (dy.splitR pH'))
| splitL_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₁ t₂) (Key.priv k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitL (dy.sdec pH kH)) (dy.splitL (dy.sdec pH' kH'))
| splitL_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₁ t₂) (Key.pub k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitL (dy.adec pH kH)) (dy.splitL (dy.adec pH' kH'))
| splitL_pair {X: TermSet} {t₁ t₂: Term} {tH tH': dy X t₁} {uH uH': dy X t₂} 
     (tN: RewriteBigStep tH tH') (uN: RewriteBigStep uH uH')
  : RewriteBigStep (dy.splitL (dy.pair tH uH)) tH'



| splitR_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH pH': dy X (Term.pair (Term.pair t₂ t₁) t₃)} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitR (dy.splitL pH)) (dy.splitR (dy.splitL pH'))
| splitR_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH pH': dy X (Term.pair t₃ (Term.pair t₂ t₁))} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitR (dy.splitR pH)) (dy.splitR (dy.splitR pH'))
| splitR_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₂ t₁) (Key.priv k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitR (dy.sdec pH kH)) (dy.splitR (dy.sdec pH' kH'))
| splitR_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₂ t₁) (Key.pub k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitR (dy.adec pH kH)) (dy.splitR (dy.adec pH' kH'))
| splitR_pair {X: TermSet} {t₁ t₂: Term} {tH tH': dy X t₁} {uH uH': dy X t₂} 
     (tN: RewriteBigStep tH tH') (uN: RewriteBigStep uH uH')
  : RewriteBigStep (dy.splitR (dy.pair tH uH)) uH'

| sdec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair (Term.enc t₁ (Key.priv k)) t₂)} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.sdec (dy.splitL pH ) kH ) (dy.sdec (dy.splitL pH') kH')
| sdec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair t₂ (Term.enc t₁ (Key.priv k)))} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.sdec (dy.splitR pH) kH) (dy.sdec (dy.splitR pH') kH')
| sdec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.priv k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.sdec (dy.sdec pH k₂H) k₁H) (dy.sdec (dy.sdec pH' k₂H') k₁H')
| sdec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.pub k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.sdec (dy.adec pH  k₂H ) k₁H ) (dy.sdec (dy.adec pH' k₂H' ) k₁H')
| sdec_senc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {k₁H k₁H': dy X (Term.key (Key.priv k))} {k₂H k₂H': dy X (Term.key (Key.priv k))} (tN: RewriteBigStep tH tH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H'): RewriteBigStep (dy.sdec (dy.senc tH k₁H) k₂H) tH'

| adec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair (Term.enc t₁ (Key.pub k)) t₂)} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.adec (dy.splitL pH ) kH ) (dy.adec (dy.splitL pH' ) kH' )
| adec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair t₂ (Term.enc t₁ (Key.pub k)))} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.adec (dy.splitR pH ) kH ) (dy.adec (dy.splitR pH' ) kH' )
| adec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.priv k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.adec (dy.sdec pH  k₂H ) k₁H ) (dy.adec (dy.sdec pH'  k₂H' ) k₁H' )
| adec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.pub k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.adec (dy.adec pH  k₂H ) k₁H ) (dy.adec (dy.adec pH'  k₂H' ) k₁H' )
| adec_aenc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {k₁H k₁H': dy X (Term.key (Key.pub k))} {k₂H k₂H': dy X (Term.key (Key.priv k))} (tN: RewriteBigStep tH tH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H'): RewriteBigStep (dy.adec (dy.aenc tH k₁H) k₂H) tH'



@[simp]
lemma dyProofRewriteSmaller: ∀ {X: TermSet} {t: Term} (proof: dy X t), 
  dyProofMeasure (dyProofRewrite proof) ≤ dyProofMeasure proof :=
  by
    intros X t proof
    cases proof with
    | splitL splitH  => 
             simp
             cases splitH with
             | pair tH uH => 
                    simp
                    omega
             | _ => simp
    
    | splitR splitH  => 
             simp
             cases splitH with
             | pair tH uH => 
                    simp
                    omega
             | _ => simp
    | sdec encH  _ => 
                simp
                cases encH with
                | senc _ _ => simp
                              omega
                | _ => simp
    | adec encH  _ => 
                simp
                cases encH with
                | aenc _ _ => simp
                              omega
                | _ => simp
    | _ => simp

@[simp]
def recursiveDyProofRewriter {X: TermSet} {t: Term} (p: dy X t) : dy X t :=
    match p with
    | dy.ax inH => dyProofRewrite (dy.ax inH)
    | dy.pk kH => dyProofRewrite (  dy.pk (recursiveDyProofRewriter kH))
    | dy.splitL splitH => dyProofRewrite ( dy.splitL (recursiveDyProofRewriter splitH))
    | dy.splitR splitH => dyProofRewrite ( dy.splitR (recursiveDyProofRewriter splitH))
    | dy.pair tH uH => dyProofRewrite (  dy.pair (recursiveDyProofRewriter tH) (recursiveDyProofRewriter uH))
    | dy.senc tH kH => dyProofRewrite (  dy.senc (recursiveDyProofRewriter tH) (recursiveDyProofRewriter kH)) 
    | dy.aenc tH kH => dyProofRewrite (  dy.aenc (recursiveDyProofRewriter tH) (recursiveDyProofRewriter kH))
    | dy.sdec encH kH => dyProofRewrite ( dy.sdec (recursiveDyProofRewriter encH) (recursiveDyProofRewriter kH))
    | dy.adec encH kH => dyProofRewrite ( dy.adec (recursiveDyProofRewriter encH) (recursiveDyProofRewriter kH))

@[simp]
def repeat_apply {A: Type} : Nat → (A → A) → A → A
| 0 => fun _ a => a 
| n + 1 => fun f a => f (repeat_apply n f a)

lemma repeatRight: ∀ {A: Type} (n: Nat) (f: A -> A) (a: A), repeat_apply (n + 1) f a = repeat_apply n f (f a) :=
  by
    intros A n f
    induction n with
    | zero => 
           intros a
           simp
    | succ n iHn =>
           intros a
           simp
           simp at iHn
           rw [iHn]
         
theorem rewriterNormaliserFun: ∀ {X: TermSet} {t: Term} (p: dy X t), isNormal (recursiveDyProofRewriter p) = true :=
  by
    
    sorry

theorem rewriterNormaliser: ∀ {X: TermSet} {t: Term} (p p': dy X t), RewriteBigStep p p' → NormalProof p' :=
  by
    intros X t p p' RW
    induction RW 
    any_goals (constructor <;> assumption)
    all_goals (assumption)


inductive SubTerm: Term -> Term -> Prop
| refl (t: Term) : SubTerm t t
                                                                                  
| pair_left (t₁ t₂: Term) : SubTerm t₁ (Term.pair t₁ t₂)
| pair_right (t₁ t₂: Term) : SubTerm t₂ (Term.pair t₁ t₂)
                                            
| enc_term (t : Term) (k: Key) : SubTerm t (Term.enc t k)
| enc_key (t: Term) (k: Key) : SubTerm (Term.key k) (Term.enc t k)

| trans_pair_left {t₁ t₂: Term} {p: Term} (sub: SubTerm p t₁): SubTerm p (Term.pair t₁ t₂)
| trans_pair_right {t₁ t₂: Term} {p: Term} (sub: SubTerm p t₂) : SubTerm p (Term.pair t₁ t₂)
                                            
| trans_enc_term {t : Term} {k: Key} {p: Term} (sub: SubTerm p t): SubTerm p (Term.enc t k)
| trans_enc_key {t: Term} {k: Key} {p: Term} (sub: SubTerm p (Term.key k)): SubTerm p (Term.enc t k)

def SubTermSet (S: TermSet) : Set Term := {x | ∃ t, t ∈ S ∧ SubTerm x t}


def ProofTerms {X: TermSet} {t: Term} (p: dy X t) : TermSet :=
  match p with
  | @dy.ax _ t _ => {t}
  | @dy.pk _ k kH => {Term.key (Key.pub k)} ∪ (ProofTerms kH)
  | @dy.splitL _ t1 _ splitH =>  {t1} ∪ (ProofTerms splitH)
  | @dy.splitR _ _ t2 splitH =>  {t2} ∪ (ProofTerms splitH)
  | @dy.pair _ t1 t2 t1H t2H => {Term.pair t1 t2} ∪ (ProofTerms t1H) ∪ (ProofTerms t2H)
  | @dy.sdec _ t' _ encH kH => {t'} ∪  (ProofTerms encH) ∪ (ProofTerms kH)
  | @dy.senc _ t' k tH kH =>   {Term.enc t' (Key.priv k)} ∪  (ProofTerms tH) ∪ (ProofTerms kH)
  | @dy.adec _ t' _ encH kH => {t'} ∪  (ProofTerms encH) ∪ (ProofTerms kH)
  | @dy.aenc _ t' k tH kH =>   {Term.enc t' (Key.pub k)} ∪  (ProofTerms tH) ∪ (ProofTerms kH)

theorem SubTermProperty: forall (X: TermSet) (t: Term) (p: dy X t), ((isNormal p) = true)
                                                                       -> match p  with
                                                                          | dy.pair _ _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | dy.senc _ _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | dy.aenc _ _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | dy.pk _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | _ => ProofTerms p ⊆ SubTermSet X
                                                                          :=
        by
          sorry


inductive Assertion: Type
| eq (t u: Term)
| member (t₀: Term) (tlist: List Term)
| and (a₀ a₁ : Assertion)
| exist (a: Assertion) (x: Var)
| says (k: Name) (a: Assertion)
deriving DecidableEq



def FVSetAssertion (a: Assertion): Set Var :=
  match a with
  | Assertion.eq l r => FVSetTerm l ∪ FVSetTerm r
  | Assertion.member t tlist => FVSetTerm t ∪ List.foldr (fun t s => FVSetTerm t ∪ s) ∅ tlist
  | Assertion.and a₀ a₁ => FVSetAssertion a₀ ∪ FVSetAssertion a₁
  | Assertion.exist a x => FVSetAssertion a \ {x}
  | Assertion.says _ a => FVSetAssertion a

def FVSetTermSet (S: TermSet) : Set Var :=
  {x | ∃ t, t ∈ S ∧ x ∈ FVSetTerm t}

abbrev AssertionSet := Set Assertion

def FVSetAssertionSet (A: AssertionSet): Set Var :=
  {x | ∃ a, a ∈ A ∧ x ∈ FVSetAssertion a}


inductive TermSubTermPosition: Term → Term → List ℕ → Prop
| epsilon (t: Term): TermSubTermPosition t t []
| pair_left₀ {t t₁ t₂: Term} {pos: List ℕ} (proof: TermSubTermPosition t (Term.pair t₁ t₂) pos) : TermSubTermPosition t t₁ (0::pos)
| pair_right₁ {t t₁ t₂: Term} {pos: List ℕ} (proof: TermSubTermPosition t (Term.pair t₁ t₂) pos) : TermSubTermPosition t t₁ (0::pos)
| enc_term₀ (t t': Term) (k: Key) {pos: List ℕ} (proof: TermSubTermPosition t (Term.enc t' k) pos) : TermSubTermPosition t t' (0::pos)
| enc_name₁ (t t': Term) (k: Key) {pos: List ℕ} (proof: TermSubTermPosition t (Term.enc t' k) pos) : TermSubTermPosition t (Term.key k) (1::pos)

def TermPositionSet (t: Term) : Set (List ℕ):=
  {pos | ∃ t', TermSubTermPosition t t' pos}

inductive AssertionTermPosition: Assertion -> Term -> List ℕ -> Prop
| eq_left0 {t tsub: Term} {pos: List ℕ} (proof: TermSubTermPosition t tsub pos) (t': Term) : AssertionTermPosition (Assertion.eq t t') tsub (0::pos)
| eq_right₁ {t t' t'sub: Term} {pos: List ℕ} (t: Term)(proof: TermSubTermPosition t t'sub pos) : AssertionTermPosition (Assertion.eq t t') t'sub (1::pos)
| member_member₀  (t: Term) (tlist: List Term) : AssertionTermPosition (Assertion.member t tlist) t [0]
| member_disjunctionSi {i: Nat} {t: Term} {tlist: List Term} (t': Term) (proof: tlist[i]? = Option.some t): AssertionTermPosition (Assertion.member t' tlist) t' [(Nat.succ i)]
                                                                                                                                                        
| and_left₀ {a : Assertion} {tsub: Term} {pos: List Nat} (a' : Assertion) (proof: AssertionTermPosition a tsub pos) : AssertionTermPosition (Assertion.and a a') tsub (0::pos)
| and_right₁ {a': Assertion} {tsub: Term} {pos: List ℕ} (a: Assertion) (proof: AssertionTermPosition a' tsub pos) : AssertionTermPosition (Assertion.and a a') tsub (1::pos)

| exist_var₀ {a: Assertion} {pos: List Nat} {tsub: Term} {x: Var}  (proof: AssertionTermPosition a (var_to_term x) pos) : AssertionTermPosition (Assertion.exist a x) (var_to_term x) (0::pos)

| says_name₀₀ (k: Name) (a: Assertion): AssertionTermPosition (Assertion.says k a) (Term.name k) [0,0]
| says_key₀ (k: Name) (a: Assertion): AssertionTermPosition (Assertion.says k a) (Term.key (Key.pub k)) [0]
| says_ass₁ {a: Assertion} (k: Name) {tsub: Term} {pos: List ℕ} (proof: AssertionTermPosition a tsub pos): AssertionTermPosition (Assertion.says k a) tsub (1::pos)

def AssertionPositionSet (a: Assertion) : Set (List ℕ):=
  {pos | ∃ t', AssertionTermPosition a t' pos}

def AssertionTermPositionSet (a: Assertion) (t: Term) : Set (List ℕ) :=
  {pos | AssertionTermPosition a t pos}

inductive ProperPrefix: List ℕ -> List ℕ -> Prop
| hd (hd: Nat) {tl: List Nat} (nonempty: tl ≠ []) : ProperPrefix [hd] (hd::tl)
| cons {hd: Nat} {tl1 tl2: List Nat} (proof: ProperPrefix tl1 tl2) : ProperPrefix (hd::tl1) (hd::tl2)

def AssertionSubTerm (a: Assertion) (t: Term) := ∃ pos, AssertionTermPosition a t pos

def AssertionSubTermSet (a: Assertion) : TermSet := {t | AssertionSubTerm a t}
def AssertionSetSubTermSet (A: AssertionSet) : TermSet:= {t | ∃ a, a ∈ A ∧ AssertionSubTerm a t}



def AssertionMaximalSubTerm (a: Assertion) (t: Term) :=
 ∃ pos, (AssertionTermPosition a t pos ∧ (¬ (∃ t' pos', AssertionTermPosition a t' pos' ∧ ProperPrefix pos' pos)))

def QSet (pos: List ℕ) : Set (List ℕ) :=
{ pos' | pos' = [] ∨ ProperPrefix pos' pos }

inductive AbstractablePositionSetTerm : TermSet → Term → Set (List ℕ)
| cons {S: TermSet} {t: Term} {p: List ℕ} (positionTermProof: p ∈(TermPositionSet t))(abstractableProof: forall (q: List Nat) (t': Term), q ∈ (QSet p) -> TermSubTermPosition t t' q -> dy S t') : AbstractablePositionSetTerm S t p

inductive AbstractablePositionSetAssertion: TermSet -> Assertion -> Set (List ℕ)
| eq_left₀ {S: TermSet} {t₀: Term} {pos: List ℕ} (t₁: Term) (proof: AbstractablePositionSetTerm S t₀ pos) : AbstractablePositionSetAssertion S (Assertion.eq t₀ t₁) (0::pos)
| eq_right₁ {S: TermSet} {t₁: Term} {pos: List ℕ} (t₀: Term) (proof: AbstractablePositionSetTerm S t₁ pos): AbstractablePositionSetAssertion S (Assertion.eq t₀ t₀) (1::pos)
| member₀ (S: TermSet) {n: ℕ} (t₀: Term) (tList : List Term) : AbstractablePositionSetAssertion S (Assertion.member t₀ tList) [0]
| and_left₀ {S:TermSet} {a : Assertion} {pos: List ℕ} (proof: pos ∈ (AbstractablePositionSetAssertion S a)) (a' : Assertion): AbstractablePositionSetAssertion S (Assertion.and a a') (0::pos)
| and_right₁ {S: TermSet} {a': Assertion} {pos: List ℕ} (a: Assertion) (proof: pos ∈ AbstractablePositionSetAssertion S a'): AbstractablePositionSetAssertion S (Assertion.and a a') (1::pos)
| exists_var₀ {S: TermSet} {pos: List ℕ} (a: Assertion) {x: Var} (proof: pos ∈ AbstractablePositionSetAssertion ( S ∪ {var_to_term x}) a):
  AbstractablePositionSetAssertion S (Assertion.exist a x)
    (0::pos)
| says_pub₀ (S: TermSet) (k: Name) (a: Assertion) : AbstractablePositionSetAssertion S (Assertion.says k a) [0]
| says_ass₁ {S: TermSet} (k: Name) {a: Assertion} {pos: List ℕ} (proof: pos ∈ AbstractablePositionSetAssertion S a): AbstractablePositionSetAssertion S (Assertion.says k a) (1::pos)



inductive SubstitutedAssertion: Assertion -> Set (List ℕ) -> Term -> Assertion -> Type
-- | cons
--     {a a': Assertion} {t: Term} {P: Set (List ℕ)}
--     (includedProof:  P ⊆ (AssertionPositionSet a))
--     (termPositionSubstitutedProof: ∀ pos,
--          pos ∈ P -> AssertionTermPosition a' t pos
--     )
--     (termPositionSameProof: forall pos t',
--         ¬(pos ∈ P) -> AssertionTermPosition a t pos -> AssertionTermPosition a' t' pos
--     )
--   : SubstitutedAssertion a P t a'.

inductive ListIntersection {A: Type} [BEq A]: List A -> List A -> List A -> Prop
| null (l: List A): ListIntersection [] l []
| new_in {hd: A} {tl l intersect: List A} (proofIntersect: ListIntersection tl l intersect) (proof: hd ∈ l ∧ (hd ∉ intersect)): ListIntersection (hd::tl) l (hd::intersect)
| new_not {hd: A} {tl l intersect: List A} (proofIntersect: ListIntersection tl l intersect) (proof: (hd ∉ l) ∨ (hd ∈ intersect) ): ListIntersection (hd::tl) l intersect


def intersection {A: Type} [BEq A]: List A -> List A -> List A
| [], _ => []
| hd::tl, l => if l.contains hd && !((intersection tl l).contains hd) 
               then hd::(intersection tl l)
               else intersection tl l

 
mutual                   
inductive eq_ady: TermSet -> AssertionSet -> Assertion -> Type
| ax (S: TermSet) {A: AssertionSet} {alpha: Assertion} (proof: alpha ∈ A): eq_ady S A alpha
| eq {S: TermSet} (A: AssertionSet) {t: Term} (proof: dy S t) : eq_ady S A (Assertion.eq t t)
                                                                     
| cons_pair {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p1: eq_ady S A (Assertion.eq t1 u1)) (p2: eq_ady S A (Assertion.eq t2 u2)): eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))

| cons_enc {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Key} (p1: eq_ady S A (Assertion.eq t1 t2)) (p2: eq_ady S A (Assertion.eq ((Term.key k1)) (Term.key k2 ))): eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))

| sym {S: TermSet} {A: AssertionSet} {t u: Term} (p: eq_ady S A (Assertion.eq t u)) : eq_ady S A (Assertion.eq u t)

| trans {S: TermSet} {A: AssertionSet} {t1 tk: Term} (p: Eq_Trans S A t1 tk): eq_ady S A (Assertion.eq t1 tk)

-- | proj_pair_left {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) (pin: [0,0] ∈ (AbstractablePositionSetAssertion S (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) ) : eq_ady S A (Assertion.eq t1 u1)
-- | proj_pair_right {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2)))  (pin: [0,1] ∈ (AbstractablePositionSetAssertion S (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) ) : eq_ady S A (Assertion.eq t2 u2)
                                   
          
-- | proj_enc_term {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) (pin: [0,0] ∈ (AbstractablePositionSetAssertion S (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) ): eq_ady S A (Assertion.eq t1 t2)
-- | proj_enc_key {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) (pin: [0,1] ∈ (AbstractablePositionSetAssertion S (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) ): eq_ady S A (Assertion.eq ((Term.key k1)) (Term.key k2 ))

-- | subst {S: TermSet} {A: AssertionSet} {t u: Term} {l: List Term} (proofMember: eq_ady S A (Assertion.member t l)) (proofEq: eq_ady S A (Assertion.eq t u)): eq_ady S A (Assertion.member u l)

-- | prom {S: TermSet} {A: AssertionSet} {t n: Term} (proof: eq_ady S A (Assertion.member t [n])) : eq_ady S A (Assertion.eq t n)

-- | int {S: TermSet} {A: AssertionSet} {t: Term} {l: List Term} (premises: Eq_ValidIntPremiseList S A t l): eq_ady S A (Assertion.member t l)
-- | wk {S: TermSet} {A: AssertionSet} {t n: Term} {nlist: List Term} (proofEq: eq_ady S A (Assertion.eq t n)) (proofIn: n ∈ nlist) (proofValid: Eq_DerivableTermsList S nlist): eq_ady S A (Assertion.member t nlist)

inductive Eq_Trans: TermSet -> AssertionSet -> Term -> Term -> Type
| two_trans {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (p1: eq_ady S A (Assertion.eq t1 t2)) (p2: eq_ady S A (Assertion.eq t2 t3)): Eq_Trans S A t1 t3
| trans_trans {S: TermSet} {A: AssertionSet} {t1 tk tk': Term} (phead: eq_ady S A (Assertion.eq t1 tk)) (plist: Eq_Trans S A tk tk'): Eq_Trans S A t1 tk'                                                           
-- inductive Eq_ValidIntPremiseList: TermSet -> AssertionSet -> Term -> List Term -> Type
-- | two_lists {S: TermSet} {A: AssertionSet} {t: Term} {l1 l2: List Term}  (proof1: eq_ady S A (Assertion.member t l1)) (proof2: eq_ady S A (Assertion.member t l2)): Eq_ValidIntPremiseList S A t (intersection l1 l2)
-- | new_list {S: TermSet} {A: AssertionSet} {t: Term} {l l': List Term} (proof1: eq_ady S A (Assertion.member t l)) (proof2: Eq_ValidIntPremiseList S A t l'): Eq_ValidIntPremiseList S A t (intersection l l')
                                                                                                                                                                                                                                                                             
-- inductive Eq_DerivableTermsList: TermSet -> List Term -> Type
-- | single {S: TermSet} {t: Term} (proof: dy S t): Eq_DerivableTermsList S [t]
-- | new {S: TermSet} {t: Term} {tlist: List Term} (proofNew: dy S t) (proofList: Eq_DerivableTermsList S tlist): Eq_DerivableTermsList S (t::tlist)
end


def isCons {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Bool :=
  match p with
  | eq_ady.cons_pair _ _ => Bool.true
  | eq_ady.cons_enc _ _ => Bool.true
  | _ => Bool.false



def foldrEqTransList {X: Type} {S: TermSet} {A: AssertionSet} {t1: Term} {tn: Term} (f: forall (S': TermSet) (A': AssertionSet) (t1: Term) (t2: Term), eq_ady S' A' (Assertion.eq t1 t2) -> X -> X) (fuel: Eq_Trans S A t1 tn) (ember: X) : X :=
  match fuel with
  | @Eq_Trans.two_trans _ A t1 t2 t3 p1 p2 => f S A t1 t2 p1 (f S A t2 t3 p2 ember)
  | @Eq_Trans.trans_trans _ A t1 tk tk' phead plist => f S A t1 tk phead (foldrEqTransList f plist ember)
  




-- noncomputable def containsCons {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): Bool :=
--   match proof with
--   | eq_ady.ax .. => false
--   | eq_ady.eq .. => false
--   | eq_ady.cons_pair .. => true
--   | eq_ady.cons_enc .. => true
--   | eq_ady.sym p => containsCons p
--   | eq_ady.trans plist =>
--                     by
--                     apply @Eq_Trans.rec _ _ (fun _ _ => Bool) (fun _ _ _ => Bool)
--                     case ax => {
                    
                    
                         
                 -- by
                 -- induction plist with
                 -- | Eq_Trans.two_trans p1 p2 => apply containsCons p1 || containsCons p2
                 -- | Eq_Trans.trans_trans p plist => sorry
