--------------------------------------------------------------------------------

-- exercise [mul-eval] (recommended)

-- using the evaluator, confirm that two times two is four

⊢2*2 : ∅ ⊢ (mul · two · two) ⦂ `ℕ
⊢2*2 = mul-type · ⊢two · ⊢two
  where
    ⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
    ⊢two = ⊢suc (⊢suc ⊢zero)

private
  one = `suc `zero
  aˢ = "a"
  aᵛ = ` aˢ
  bˢ = "b"
  bᵛ = ` bˢ
  mˢ = "m"
  mᵛ = ` mˢ
  nˢ = "n"
  nᵛ = ` nˢ
  +ˢ = "+"
  +ᵛ = ` +ˢ
  *ˢ = "*"
  *ᵛ = ` *ˢ

_ : eval (gas 100) ⊢2*2 ≡
  steps
  ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ `zero |suc mˢ ⇒
      (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · nᵛ
      · (*ᵛ · mᵛ · nᵛ)
      ])))
   · two
   · two
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ mˢ ⇒ (ƛ nˢ ⇒
     case mᵛ [zero⇒ `zero |suc mˢ ⇒
     (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · nᵛ
     ·
     ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ `zero |suc mˢ ⇒
         (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
            case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
            ])))
         · nᵛ
         · (*ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ]))
   · two
   · two
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ `zero |suc mˢ ⇒
    (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · nᵛ
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   · two
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
   case two [zero⇒ `zero |suc mˢ ⇒
   (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
      case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
      ])))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · two)
   ]
   —→⟨ β-suc (V-suc V-zero) ⟩
   (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
      case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
      ])))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ aˢ ⇒ (ƛ bˢ ⇒
     case aᵛ [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ]))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ `zero |suc mˢ ⇒
      (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · nᵛ
      ·
      ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ `zero |suc mˢ ⇒
          (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
             case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
             ])))
          · nᵛ
          · (*ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ]))
    · one
    · two)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case one [zero⇒ `zero |suc mˢ ⇒
     (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · nᵛ
     ·
     ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ `zero |suc mˢ ⇒
         (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
            case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
            ])))
         · nᵛ
         · (*ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    · two)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   case one [zero⇒ `zero |suc mˢ ⇒
   (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
      case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
      ])))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · two)
   ]
   —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · two
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ aˢ ⇒ (ƛ bˢ ⇒
      case aᵛ [zero⇒ bᵛ |suc aˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · aᵛ
       · bᵛ)
      ]))
    · two
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ bˢ ⇒
     case two [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ bˢ ⇒
     case two [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    ·
    ((ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · nᵛ
       ·
       ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ `zero |suc mˢ ⇒
           (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
              case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
              ])))
           · nᵛ
           · (*ᵛ · mᵛ · nᵛ)
           ])))
        · mᵛ
        · nᵛ)
       ]))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ bˢ ⇒
     case two [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    ·
    ((ƛ nˢ ⇒
      case `zero [zero⇒ `zero |suc mˢ ⇒
      (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · nᵛ
      ·
      ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ `zero |suc mˢ ⇒
          (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
             case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
             ])))
          · nᵛ
          · (*ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ])
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ bˢ ⇒
     case two [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    ·
    case `zero [zero⇒ `zero |suc mˢ ⇒
    (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · two
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · two)
    ])
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   ((ƛ bˢ ⇒
     case two [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   case two [zero⇒ `zero |suc aˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · aᵛ
    · `zero)
   ]
   —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · one
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   ((ƛ aˢ ⇒ (ƛ bˢ ⇒
      case aᵛ [zero⇒ bᵛ |suc aˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · aᵛ
       · bᵛ)
      ]))
    · one
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   ((ƛ bˢ ⇒
     case one [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   case one [zero⇒ `zero |suc aˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · aᵛ
    · `zero)
   ]
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   (`suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · `zero
     · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   (`suc
    ((ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒
       `suc
       ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · aᵛ
        · bᵛ)
       ]))
     · `zero
     · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   (`suc
    ((ƛ bˢ ⇒
      case `zero [zero⇒ bᵛ |suc aˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · aᵛ
       · bᵛ)
      ])
     · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   ·
   `suc
   (`suc
    case `zero [zero⇒ `zero |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · `zero)
    ])
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
   (ƛ bˢ ⇒
    case two [zero⇒ bᵛ |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · bᵛ)
    ])
   · two
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
   case two [zero⇒ two |suc aˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · aᵛ
    · two)
   ]
   —→⟨ β-suc (V-suc V-zero) ⟩
   `suc
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   `suc
   ((ƛ aˢ ⇒ (ƛ bˢ ⇒
      case aᵛ [zero⇒ bᵛ |suc aˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · aᵛ
       · bᵛ)
      ]))
    · one
    · two)
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
   `suc
   ((ƛ bˢ ⇒
     case one [zero⇒ bᵛ |suc aˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
         case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
         ])))
      · aᵛ
      · bᵛ)
     ])
    · two)
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
   `suc
   case one [zero⇒ two |suc aˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
       ])))
    · aᵛ
    · two)
   ]
   —→⟨ ξ-suc (β-suc V-zero) ⟩
   `suc
   (`suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   `suc
   (`suc
    ((ƛ aˢ ⇒ (ƛ bˢ ⇒
       case aᵛ [zero⇒ bᵛ |suc aˢ ⇒
       `suc
       ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
           case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
           ])))
        · aᵛ
        · bᵛ)
       ]))
     · `zero
     · two))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
   `suc
   (`suc
    ((ƛ bˢ ⇒
      case `zero [zero⇒ bᵛ |suc aˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
          case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
          ])))
       · aᵛ
       · bᵛ)
      ])
     · two))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   `suc
   (`suc
    case `zero [zero⇒ two |suc aˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ aˢ ⇒ (ƛ bˢ ⇒
        case aᵛ [zero⇒ bᵛ |suc aˢ ⇒ `suc (+ᵛ · aᵛ · bᵛ)
        ])))
     · aᵛ
     · two)
    ])
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc (`zero)))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
