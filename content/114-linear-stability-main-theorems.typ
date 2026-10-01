#import "main-defs.typ": E, GE, GL, K, SK, SL, SR, name-idx, source, symbol-idx
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, theorem,
  variant-proposition,
)

== Основные теоремы <sec:linear-stability-main-theorems>

Зафиксируем кольцо $A$. Если $frak(q)$ — двусторонний идеал, то через
$GL'_m (A, frak(q))$#symbol-idx(
  $GL'_m (A, frak(q))$,
  sort: "GL'_m(A,q)",
  group: "groups",
  order: 103,
) обозначим полный прообраз в группе $GL_m (A)$ центра группы
$GL_m (A slash frak(q))$.

#source(197)#theorem[
  Допустим, что выполнено условие $SR_n (A)$ (см. определение
  @def:relative-stable-rank), и пусть $m >= n$. Тогда для любого двустороннего
  идеала $frak(q)$:
  #condition-list[
    #condition-item(format: "cyrillic")[$E_m (A, frak(q))$ является нормальным
      делителем группы $GL_m (A)$ и
      $GL_m (A, frak(q)) = E_m (A, frak(q)) dot GL_(n - 1) (A, frak(q))$.]
    <cond:linear-relative-elementary-normality>

    #condition-item(format: "cyrillic")[$[GE_m (A), GL_m (A, frak(q))]
      subset E_m (A, frak(q))$. Если $m >= 3$, то это включение превращается в
      равенство, и, кроме того,
      $
        [E_m (A), GL'_m (A, frak(q))] = E_m (A, frak(q)).
      $
      Если $m >= 2(n - 1)$#footnote[
        Это условие излишне, см. Васерштейн @bib:Vaserstein1969c.#name-idx(
          "Васерштейн Л. Н.",
        ) — _Прим. ред._
      ], то
      $
        [GL_m (A), GL_m (A, frak(q))] subset E_m (A, frak(q)).
      $
    ] <cond:linear-relative-commutator-formulas>

    #condition-item(format: "cyrillic")[Допустим, что $m >= 3$. В этом случае
      подгруппа $H$ группы $GL_m (A)$ нормализуется группой $E_m (A)$ тогда и
      только тогда, когда существует двусторонний идеал $frak(q)$, такой, что
      $
        E_m (A, frak(q)) subset H subset GL'_m (A, frak(q)).
      $
      В этой ситуации идеал $frak(q)$ определяется равенством
      $
        E_m (A, frak(q)) = [E_m (A), H].
      $
    ] <cond:linear-normalized-subgroup-level>
  ]
] <th:linear-normal-subgroup-stability>

Эта теорема будет доказана в §~@sec:linear-stability-first-proof. Из
доказательств утверждений @cond:linear-relative-elementary-normality и
@cond:linear-relative-commutator-formulas теоремы будет следовать

#variant-proposition[
  Допустим, что выполнено лишь условие $SR_n (A, frak(q))$, и пусть $m >= n$.
  Тогда $GL_m (A, frak(q)) = E_m (A, frak(q)) dot GL_(n - 1) (A, frak(q))$ и
  $[GE_m (A), GL_m (A, frak(q))] subset E_m (A, frak(q))$, причем для $n >= 3$
  имеет место равенство.
] <prop:relative-linear-normal-subgroup-stability>

#theorem[
  Пусть $frak(q)$ — двусторонний идеал кольца $A$. Допустим, что выполнены
  условия $SR_n (A, frak(q))$, $SR_n (A^o, frak(q))$ и
  $SR'_(n - 1) (A, frak(q))$#footnote[
    Условия $SR_n (A, frak(q))$ и $SR_n (A^o, frak(q))$ эквивалентны (см.
    Васерштейн @bib:Vaserstein1971), а условие $SR'_(n - 1) (A, frak(q))$ здесь
    излишне (см. Васерштейн @bib:Vaserstein1969c). — _Прим. ред._
  ]. Тогда отображение
  $
    GL_(n - 1) (A, frak(q)) -> K_1 (A, frak(q))
  $
  сюръективно и для $m >= n$ естественный гомоморфизм
  $
    GL_m (A, frak(q)) slash E_m (A, frak(q)) -> K_1 (A, frak(q))
  $
  является изоморфизмом.
] <th:relative-k1-stability>

Напомним, что $K_1 (A, frak(q)) = GL(A, frak(q)) slash E(A, frak(q))$ (см.
§~@sec:normal-subgroups-relative-k1). Таким образом, утверждение о
сюръективности отображения $GL_m (A, frak(q)) -> K_1 (A, frak(q))$ для
$m >= n - 1$ следует из теоремы @th:linear-normal-subgroup-stability
@cond:linear-relative-elementary-normality (или, точнее, из предложения
@prop:relative-linear-normal-subgroup-stability). Доказательство инъективности
отображения технически сложно и занимает
§~@sec:linear-stability-homomorphism-construction–@sec:linear-stability-final-proof.

#source(198)Если кольцо $A$ коммутативно, то из @th:relative-k1-stability
немедленно следует, что отображение
$
  SL_(n - 1) (A, frak(q)) -> SK_1 (A, frak(q))
$
сюръективно и что отображение
$
  SL_m (A, frak(q)) slash E_m (A, frak(q)) -> SK_1 (A, frak(q))
$
является изоморфизмом для всех $m >= n$. Имеются также следующие полезные
следствия.

#corollary[
  В предположениях теоремы @th:relative-k1-stability допустим к тому же, что
  выполнено условие $SR_n (A)$. Пусть $m >= n$, и пусть $H subset GL_m (A)$ —
  подгруппа уровня $frak(q)$. Тогда
  $
    E_m (A, frak(q)) supset [GL_m (A), H] supset [E_m (A), H],
  $
  причем при $m >= 3$ имеет место равенство.
] <cor:stable-linear-relative-commutators>

#proof[
  Равенство при $m >= 3$ следует из @th:linear-normal-subgroup-stability
  @cond:linear-relative-commutator-formulas. Для доказательства оставшейся части
  следствия достаточно показать, что
  $[GL_m (A), GL_m (A, frak(q))] subset E_m (A, frak(q))$. В силу утверждения
  @th:stable-linear-normal-subgroups @cond:stable-linear-relative-commutators
  $[GL(A), GL(A, frak(q))] = E(A, frak(q))$. Из части теоремы
  @th:relative-k1-stability, касающейся инъективности, вытекает, что
  $E(A, frak(q)) inter GL_m (A) = E_m (A, frak(q))$. Это завершает
  доказательство следствия.
]

#corollary[
  Допустим, что в предположениях теоремы @th:relative-k1-stability $frak(q) = A$
  и $A$ — конечно порожденная $ZZ$-алгебра. Если группа $GL_m (A)$ конечно
  порождена для некоторого $m >= n - 1$, то $K_1 (A)$ — конечно порожденная
  абелева группа. Обратно, если группа $K_1 (A)$ конечно порождена, то
  $GL_m (A)$ — конечно порожденная группа для всех $m >= max(n, 3)$.
] <cor:linear-k1-finite-generation-equivalence>

#proof[
  Первое утверждение следует из того, что отображение $GL_m (A) -> K_1 (A)$
  сюръективно для $m >= n - 1$. В силу следствия
  @cor:elementary-group-finite-generation $E_m (A)$ — конечно порожденная группа
  для всех $m >= 3$. Если к тому же $m >= n$, то из теоремы
  @th:relative-k1-stability следует, что
  $GL_m (A) slash E_m (A) approx K_1 (A)$. Таким образом, если $K_1 (A)$ —
  конечно порожденная группа, то группа $GL_m (A)$ также конечно порождена.
]

*Замечание.* Если в следствии @cor:linear-k1-finite-generation-equivalence
кольцо $A$ коммутативно, то справедливо аналогичное ему утверждение с группой
$SL_m$ вместо $GL_m$ и с группой $SK_1$ вместо $K_1$. Это следует из
соответствующего аналога теоремы @th:relative-k1-stability для $SK_1$.

#corollary[
  Пусть $R$ — коммутативное кольцо, такое, что $max(R)$ — нётерово пространство,
  являющееся объединением конечного числа подпространств размерности $<= d$.
  Пусть $A$ — конечномерная $R$-алгебра. Тогда утверждения теоремы
  @th:linear-normal-subgroup-stability справедливы для кольца $A$ при
  $n = d + 2$. Утверждения теоремы @th:relative-k1-stability #source(
    199,
  )справедливы для кольца $A$ и всех идеалов $frak(q)$ при $n = d + 3$#footnote[
    И даже при $n = d + 2$, см. Васерштейн @bib:Vaserstein1969c.#name-idx(
      "Васерштейн Л. Н.",
    ) — _Прим. ред._
  ] или при $n = 3$, если алгебра $A$ коммутативна и $d = 1$.
] <cor:linear-stability-dimension-bound>

#proof[
  В силу теоремы @th:stable-rank-dimension-bound справедливо условие
  $SR_(d + 2) (A)$, а также (в силу симметрии) условие $SR_(d + 2) (A^o)$. Из
  @th:stable-rank-relative-elementary-stability
  @cond:stable-rank-elementary-transitivity вытекает, что $SR_n => SR'_n$.
  Импликация $SR_n => SR_(n + 1)$ очевидна. Следовательно, для кольца $A$
  выполнены условия $SR_(d + 3)$ и $SR'_(d + 2)$. Таким образом, мы установили
  справедливость предположений теорем @th:linear-normal-subgroup-stability и
  @th:relative-k1-stability соответственно для указанных рангов. Кроме того,
  если кольцо $A$ коммутативно, то в силу
  @prop:semilocal-commutative-stable-rank
  @cond:commutative-rank-two-transitivity всегда выполнено условие
  $SR'_2 (A, frak(q))$. Следовательно, если $d = 1$, то справедливы
  $SR_3 (= SR_(d + 2))$ и $SR'_2$, т.~е. предположения теоремы
  @th:relative-k1-stability для $n = 3$.
]

*Замечание.* Возможно, для справедливости теоремы @th:relative-k1-stability
достаточно только предположений $SR_n$#footnote[
  Это действительно так, см. Васерштейн @bib:Vaserstein1969c. — _Прим. ред._
]. Из доказательства будет видно, что предположение $SR'_(n - 1)$ используется
лишь на последнем этапе (см. @lem:linear-stability-transposition-invariance).
