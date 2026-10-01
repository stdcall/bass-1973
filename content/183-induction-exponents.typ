#import "main-defs.typ": (
  FiniteGroupCat, Frob, G, GroupCat, Im, K, Ker, U, char, idx, maxSpec,
  moduleCategory, name-idx, source, symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition,
)
#import "diagrams/finite-group-induction-basic.typ": swan-group-ring-triangle

== Индукционные экспоненты <sec:induction-exponents>

Напомним (см. §~@sec:frobenius-functors-modules), что через $GroupCat$ мы
обозначаем категорию, объекты которой — группы, а морфизмы — мономорфизмы
$j: pi' -> pi$ конечного индекса (т. е. индекс $[pi:j (pi')]$ конечен). Через
$FiniteGroupCat$ обозначена полная подкатегория конечных групп.

Зафиксируем класс $C$ объектов категории $GroupCat$. Если $R$ — коммутативное
кольцо и $pi in GroupCat$, то через
$ e_C (R,pi) $
#symbol-idx($e_C (R,pi)$, sort: "ec(R,π)", group: "groups", order: 90)
обозначим экспоненту (см. @def:group-exponent) группы $(G_R)_C (pi)$ (см.
@def:frobenius-induction-restriction-subgroups) в $G_R (pi)$. Так как последняя
группа является кольцом, а первая из групп — идеалом в нем, то $e_C (R,pi)$
совпадает с наименьшим натуральным числом $e$ (если только такое существует),
для которого $e dot [R_pi] in (G_R)_C (pi)$. Существование числа $e_C (R,pi)$
будет предполагаться, за исключением тех случаев, когда его существование явно
доказывается. Это число называется _индукционной экспонентой_#idx(
  "индукционная экспонента",
) пары $(R,pi)$ относительно класса $C$. Важность ее объясняется следующим
непосредственным следствием из «принципов индукции и ограничения»
@prop:frobenius-induction-restriction-principles:

#proposition[
  Пусть $R$ — коммутативное кольцо и $G_R: GroupCat -> Frob$ — фробениусов
  функтор (см. @exm:group-ring-frobenius-functor). Тогда для любого фробениусова
  $G_R$-модуля $K$ (например, для $K=K_i (bold(M)_0 (R pi))$ или для
  $K=K_i (R pi),i=0,1$) и для любой группы $pi in GroupCat$ экспоненты групп
  $K (pi) slash K_C (pi)$ и $K^C (pi)$ равны $e_C (R,pi)$.
] <prop:induction-exponent-module-bound>

Результаты этого параграфа описывают поведение $e_C (R,pi)$ как функции от $R$ и
от $pi$.

#source(441)
#proposition[
  Пусть $f: R' -> R$ — гомоморфизм коммутативных колец и $pi in GroupCat$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[
      Число $e_C (R,pi)$ делит число $e_C (R',pi)$.
    ] <cond:induction-exponent-scalar-extension>

    #condition-item(format: "cyrillic")[
      Если $maxSpec (R')$ — нётерово пространство размерности $<= d$ и $R$ —
      проективный $R'$-модуль (постоянного) ранга $n$, то число $e_C (R',pi)$
      делит число $e_C (R,pi) dot n^(d+1)$. Кроме того, если порядок элемента
      $n-[R]_(R')$ группы $K_0 (R')$ конечен и равен $m$, то число $e_C (R',pi)$
      делит число $e_C (R,pi) dot n dot m$.
    ] <cond:induction-exponent-scalar-transfer>
  ]
] <prop:induction-exponent-change-ring>

#proof[
  @cond:induction-exponent-scalar-extension Заметим, что $f_*: G_(R') -> G_R$ —
  морфизм фробениусовых функторов. Следовательно,
  $ f_* (e_C (R',pi) dot 1)=e_C (R',pi) dot 1 in (G_R)_C (pi). $

  @cond:induction-exponent-scalar-transfer Пусть $e=e_C (R,pi)$. В этом случае
  можно рассмотреть гомоморфизм ограничения $f^*: G_R -> G_(R')$, который
  перестановочен с гомоморфизмами ограничения и индукции, которые индуцированы
  морфизмами категории $GroupCat$ (см.
  @prop:group-ring-scalar-extension-restriction). Следовательно,
  $f^* (e dot 1)=e f^* (1) in (G_(R'))_C (pi)$. Роль элемента $1 in G_R (pi)$
  здесь играет элемент $[R]_(R pi)$. Поэтому $f^* (1)=[f^* R]_(R' pi)$. Таким
  образом, модуль $(G_(R'))_C (pi)$ содержит $e [R]_(R') dot G_(R') (pi)$, где
  $[R]_(R')$ — класс модуля $R$ в группе $K_0 (R')$. Из
  @cor:projective-free-tensor-complement-bound следует, что элемент
  $n^(d+1) dot 1$ лежит в $[R]_(R') dot K_0 (R')$. Кроме того, если
  $m ([R]_(R')-n)=0$, то там же лежит и $m [R]_(R')=m (n+([R]_(R')-n))=m n$, что
  и требовалось доказать.
]

#proposition[
  Пусть $R$ — дедекиндово кольцо с полем частных $L$. Пусть
  $frak(p) in maxSpec (R)$ и $pi$ — конечная группа, порядок которой не делится
  на $char (L)$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[
      число $e_C (R slash frak(p),pi)$ делит число $e_C (L,pi)$;
    ] <cond:induction-exponent-residue-field>

    #condition-item(format: "cyrillic")[
      число $e_C (R,pi)$ делит число $e_C (L,pi)^2$.
    ] <cond:induction-exponent-dedekind-square>
  ]
] <prop:induction-exponent-dedekind-ring>

#proof[
  В силу @th:maschke алгебра $L pi$ полупроста. Поэтому диаграмма
  $ #swan-group-ring-triangle() $
  является треугольником Суона @prop:swan-triangle, который, используя
  @prop:regular-group-ring-resolution, можно отождествить с треугольником
  $ #swan-group-ring-triangle(frobenius: true) $
  Верхнее и левое отображения индуцированы гомоморфизмами $R -> L$ и
  $R -> R slash frak(p)$ соответственно. Поэтому они являются #source(
    442,
  )морфизмами фробениусовых функторов (на категории $FiniteGroupCat$). Правое
  отображение было получено ввиду сюръективности верхнего отображения. Поэтому
  оно также оказывается морфизмом фробениусовых функторов. Таким образом,
  $e_C (L,pi) dot 1 in (G_(R slash frak(p)))_C (pi)$, что доказывает утверждение
  @cond:induction-exponent-residue-field.

  В силу @prop:dedekind-g-localization-decomposition получаем точную
  последовательность
  $
    union.sq.big_(frak(p) in maxSpec (R)) G_0 ((R slash frak(p)) pi)
    arrow.r^f G_0 (R pi) arrow.r^(g_0) G_0 (L pi) -> 0,
  $
  где отображение $f$ индуцировано «ограничениями»
  $bold(M) ((R slash frak(p)) pi) subset bold(M) (R pi)$. В частности, они
  перестановочны с гомоморфизмами индукции и ограничения, возникающими из
  морфизмов категории $FiniteGroupCat$. Пусть $e=e_C (L,pi)$. Так как
  отображение $G_0 (R pi') -> G_0 (L pi')$ сюръективно для всех подгрупп
  $pi' subset pi$, то отображение $(G_R)_C (pi) -> (G_L)_C (pi)$ также
  сюръективно. Следовательно, можно так выбрать элемент $a in (G_R)_C (pi)$, что
  $g_0 (a)=e dot 1$. Итак, $e dot 1-a in Ker (g_0)$. Поэтому $e dot 1-a=f (b)$.
  В силу части @cond:induction-exponent-residue-field предложения
  $e dot b in union.sq.big (G_(R slash frak(p)))_C (pi)$
  $(frak(p) in maxSpec (R))$. Поэтому
  $f (e dot b)=e f (b)=e^2 dot 1-e a in (G_R)_C (pi)$. Так как
  $e a in (G_R)_C (pi)$, то $e^2 dot 1 in (G_R)_C (pi)$, что и доказывает
  @cond:induction-exponent-dedekind-square.
]

#corollary[
  Для любого поля $L$ и любой конечной группы $pi$ число $e_C (L,pi)$ делит
  число $e_C (QQ,pi)$. Для любого коммутативного кольца $R$ число $e_C (R,pi)$
  делит число $e_C (QQ,pi)^2$.
] <cor:rational-induction-exponent-bound>

#proof[
  Если $char (L)=0$, то $L$ является $QQ$-алгеброй. Из
  @prop:induction-exponent-change-ring@cond:induction-exponent-scalar-extension
  в этом случае следует наше утверждение. Если $char (L)=p > 0$, то в силу
  @prop:induction-exponent-change-ring@cond:induction-exponent-scalar-extension
  утверждение достаточно доказать для простого поля $ZZ slash p ZZ$. Но в этом
  случае наше утверждение вытекает из
  @prop:induction-exponent-dedekind-ring@cond:induction-exponent-residue-field.
  Аналогично последнее утверждение следует из
  @prop:induction-exponent-dedekind-ring@cond:induction-exponent-dedekind-square,
  поскольку $R$ является $ZZ$-алгеброй.
]

Теперь зафиксируем кольцо $R$ и будем менять группу $pi$.

#proposition[
  Допустим, что каждая подгруппа конечного индекса группы из класса $C$ опять
  лежит в классе $C$. Пусть $j: pi' -> pi$ — морфизм категории $GroupCat$. Тогда
  для любого коммутативного кольца $R$ имеет место включение
  $j^* ((G_R)_C (pi)) subset (G_R)_C (pi')$. Следовательно, $(G_R)_C$ является
  фробениусовым $G_R$-подмодулем в $G_R$. Кроме того, число $e_C (R,pi')$ делит
  число $e_C (R,pi)$.
] <prop:induction-exponent-subgroup-bound>

#proof[
  Так как $j^*$ — гомоморфизм колец, то последнее утверждение вытекает из
  первого. Второе утверждение также вытекает из первого в силу
  @prop:frobenius-subgroups-properties@cond:frobenius-submodule-reciprocity.

  Пусть теперь $i: pi'' -> pi$ — морфизм в категории $GroupCat$ и $pi'' in C$.
  Предложение будет доказано, если мы покажем, что
  $j^* (Im (i_*)) subset (G_R)_C (pi')$. Для удобства отождествим $pi'$ и $pi''$
  с подгруппами группы $pi$. Таким образом, $j$ и $i$ являются вложениями. Если
  $M in bold(M)_0 (R pi'')$, то достаточно показать, что
  $j^* i_* [M] in (G_R)_C (pi')$. #source(443)Но
  $j^* i_* M=j^* (M tensor_(R pi'') R pi)$, а из теоремы Макки о подгруппах (см.
  книгу Кэртиса#name-idx("Кэртис (Curtis C. W.)") и Райнера#name-idx(
    "Райнер (Reiner I.)",
  ) @bib:Curtis1962) следует, что
  $j^* (M tensor_(R pi'') R pi) tilde.eq union.sq.big_D M (D)$, где $D$
  пробегает двойные смежные классы $D=pi'' x pi'$ и $M (D)$ — индуцированный
  модуль с морфизмами $j (D): x^(-1) pi'' x inter pi' -> pi'$, скажем
  $M (D)=j (D)_* N_D$. (Кэртис и Райнер предполагают, что $R$ — поле, но это
  нигде не используется в их доказательстве. Незначительная разница имеется лишь
  в формулировках, поскольку мы рассматриваем правые модули.) Так как индекс
  обеих подгрупп $pi''$ и $pi'$ конечен в группе $pi$, то индекс подгруппы
  $x^(-1) pi'' x inter pi'$ также конечен; при этом из нашего предположения
  следует, что эта подгруппа лежит в $C$ и изоморфна подгруппе конечного индекса
  в $pi''$. Заметим, что $j (D)_* N$ как $R$-модуль является прямой суммой
  экземпляров модуля $N$. В то же самое время он есть прямое слагаемое модуля
  $j^* i_* M$. Поэтому $N in bold(M)_0 (R [x^(-1) pi'' x inter pi'])$. Таким
  образом, $j^* i_* [M] in sum_D Im (j (D)_*) subset (G_R)_C (pi')$, что и
  требовалось доказать.
]

#proposition[
  Допустим, что если $sigma in C$, то каждая факторгруппа $sigma slash sigma'$,
  где $sigma'$ — конечный нормальный делитель, опять принадлежит классу $C$.
  Пусть $pi$ — группа и $pi'$ — конечный нормальный делитель порядка
  $n=[pi':1]$. Пусть $R$ — коммутативное кольцо, для которого $n in U (R)$.
  Тогда число $e_C (R,pi slash pi')$ делит число $e_C (R,pi)$.
] <prop:induction-exponent-normal-quotient-bound>

#proof[
  Заметим, что $R pi'=R e plus.o I$, где $e=n^(-1) sum_(x in pi') x$ —
  центральный идемпотент и $I$ — идеал пополнения. Это легко установить
  (используя @prop:maschke-relative-splitting), например, расщепляя
  последовательность
  $ 0 -> I -> R pi' -> R_(pi') -> 0. $
  Это означает, что $R pi'$ является произведением двух колец, при этом один
  сомножитель соответствует тривиальному $R pi'$-модулю $R_(pi') tilde.eq R e$.
  Следовательно, для всех $M in moduleCategory-R pi'$ имеет место каноническое
  разложение $M e plus.o M I$ как $R pi'$-модулей. В частности, функтор
  $tensor_(R pi') R_(pi')$ оказывается точным.

  Пусть $J=R pi dot I$. Так как $pi'$ — нормальный делитель в $pi$, то $J$ —
  двусторонний идеал в кольце $R pi$. Ясно, что $pi'$ переходит в $1$ в кольце
  $R pi slash J$. С другой стороны, ясно, что $I subset Ker (R pi -> R pi'')$,
  где $pi''=pi slash pi'$. Поэтому $R pi''=R pi slash J$. Но если
  $M in moduleCategory-R pi$, то
  $M tensor_(R pi) R pi''=M slash M J=M slash M dot R pi dot I
  =M slash M I=M tensor_(R pi') R_(pi')$. Таким образом, функтор
  $tensor_(R pi) R pi''$ точен (согласно выводу, сделанному в первом абзаце
  доказательства). Теперь очевидно, что если $M$ — конечно порожденный #source(
    444,
  )проективный $R$-модуль, то таким же является и $R$-модуль
  $M tensor_(R pi) R pi''$, который изоморфен прямому слагаемому $M e$ в $M$.
  Итак, мы получаем точный функтор
  $tensor_(R pi) R pi'': bold(M)_0 (R pi) -> bold(M)_0 (R pi'')$, и,
  следовательно, аддитивное отображение $p: G_R (pi) -> G_R (pi'')$, переводящее
  единицу в единицу.

  Пусть $j: sigma -> pi$ — морфизм в категории $GroupCat$ и $sigma in C$. Если
  мы сможем показать, что $p (Im (j_*)) subset (G_R)_C (pi'')$, то тогда
  $p ((G_R)_C (pi)) subset (G_R)_C (pi'')$ и утверждение предложения будет
  следовать отсюда.

  Пусть $sigma'=j^(-1) (pi')$ (конечный нормальный делитель группы $sigma$),
  $sigma''=sigma slash sigma'$ и $j'': sigma'' -> pi''$ — индуцированный
  мономорфизм (конечного индекса). Из наших предположений о классе $C$ следует,
  что $sigma'' in C$. Таким образом, достаточно установить существование
  естественного изоморфизма
  $ (j_* M) tensor_(R pi) R pi'' tilde.eq j''_* (M tensor_(R sigma) R sigma'') $
  $R pi''$-модулей для $M in moduleCategory-R sigma$. Именно мы хотели бы
  установить изоморфизм $(M tensor_(R sigma) R pi) tensor_(R pi) R pi'' tilde.eq
  (M tensor_(R sigma) R sigma'') tensor_(R sigma'') R pi''$. Но оба входящие
  сюда модуля изоморфны модулю $M tensor_(R sigma) R pi''$, что и требовалось
  доказать.
]
