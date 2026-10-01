#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/polynomial-fundamental-theorem-group-rings.typ": (
  conductor-k-augmentation-square, quasiregular-k-zero-square,
  quasiregular-pullback-square, quasiregular-relative-determinant,
)

== Групповые кольца абелевых групп <sec:abelian-group-rings>

В этом параграфе мы применим развитую теорию для вычисления групп $K_0$ и $K_1$
в ряде частных случаев. В их число входят групповые кольца $ZZ pi$, где $pi$ —
конечно порожденная абелева группа.

Зафиксируем ориентированный цикл $(T,T_±)$. Далее, назовем кольцо $A$ #idx(
  "квазирегулярное кольцо",
)_квазирегулярным_, если оно содержит двусторонний нильпотентный идеал $J$, для
которого кольцо $A/J$ регулярно справа. Таким образом, артиновы справа кольца
являются квазирегулярными. Из теорем Гильберта о базисе и о сизигиях следует,
что кольца $A[T_+^n]$ и $A[T^n]$ квазирегулярны для всех $n >= 0$, если
квазирегулярно кольцо $A$.

#proposition[
  Если кольцо $A$ квазирегулярно, то $L^n N^i K_0 (A)=0$ для $n > 0$ или
  $i > 0$. Если к тому же кольцо $A$ коммутативно, то отображение
  $ N^i det: N^i K_1 (A) -> N^i U(A) $
  является изоморфизмом, и поэтому $N^i SK_1 (A)=0$ для всех $i > 0$.
] <prop:quasiregular-k-functor-vanishing>

#proof[
  Пусть $F=L^n N^i K_0$, где $n,i >= 0$. Тогда группы $N F(A)$ и $L F(A)$
  являются прямыми слагаемыми в $F(A[T])$. Как было замечено выше, кольцо $A[T]$
  квазирегулярно. Следовательно, проводя индукцию по $(n,i)$, достаточно
  доказать, что $N K_0 (A)=0=L K_0 (A)$ для квазирегулярного кольца $A$. Это
  будет доказывать первое утверждение предложения.

  #source(521)Пусть $J$ — нильпотентный двусторонний идеал кольца $A$ и кольцо
  $B=A/J$ регулярно справа. В коммутативной диаграмме
  #quasiregular-k-zero-square()
  отображения нижней строки являются изоморфизмами (в силу теоремы Серра
  @th:regular-polynomial-k-zero). По @prop:k-radical-ideal-comparison
  @cond:k-zero-radical-quotient-injection, все вертикальные отображения —
  изоморфизмы. Следовательно, отображения верхней строки также являются
  изоморфизмами. Теперь непосредственно из определений следует, что
  $N K_0 (A)=0=L K_0 (A)$.

  Что касается последнего утверждения, то отображение
  $N^i det: N^i K_1 (A) -> N^i U(A)$ оказывается изоморфизмом, если кольцо $A$
  коммутативно и квазирегулярно (можно рассуждать как и выше, проводя индукцию
  по $i$ и сводя рассмотрение к случаю $i=1$). Тогда во введенных выше
  обозначениях получаем коммутативную диаграмму с точными строками:
  #quasiregular-relative-determinant()
  Справа стоят нулевые группы, поскольку идеал $J$ нильпотентен. Из
  @cor:regular-polynomial-k-one следует, что вертикальное отображение,
  расположенное справа, изоморфно отображению $K_1 (B) -> U(B)$. Следовательно,
  $N K_1 (B)=0$. Таким образом, рассматривая диаграмму, получаем, что
  отображение $det: N K_1 (A) -> N U(A)$ изоморфно ядру морфизма гомоморфизмов
  $
    (K_1 (A[T_+],J A[T_+]) arrow.r^(det) U(A[T_+],J A[T_+]))
    -> (K_1 (A,J) arrow.r^(det) U(A,J)),
  $
  соответствующему пополнению $A[T_+] -> A$. Так как идеалы $J$ и $J A[T_+]$
  нильпотентны, то из @prop:relative-sk-one-exact-sequences следует, что оба
  рассмотренные отображения $det$ являются изоморфизмами, и, следовательно, этим
  же свойством обладает и их ядро. Утверждение доказано.
]

#proposition[
  Пусть диаграмма
  #quasiregular-pullback-square()
  #source(522)является декартовым квадратом гомоморфизмов колец, в котором
  отображения $f_1$ и $f_2$ сюръективны. Допустим, что кольца $A_1,A_2$ и $A'$
  квазирегулярны. Тогда
  #condition-list[
    #condition-item[$L^n N^i K_0 (A)=0$, если $n > 0$ и $i > 0$ или если $n > 1$
      и $i >= 0$;] <cond:quasiregular-pullback-k-vanishing>
    #condition-item[$L K_0 (A)=Coker (K_0 (A_1) plus.o K_0 (A_2) -> K_0 (A'))$;]
    <cond:quasiregular-pullback-contracted-k-zero>
    #condition-item[$N^i K_0 (A)=Coker (N^i K_1 (A_1) plus.o N^i K_1 (A_2)
        -> N^i K_1 (A'))$ для $i > 0$.] <cond:quasiregular-nil-k-zero-cokernel>
  ]
  Если рассмотренные выше кольца коммутативны, то
  #variant-condition[$N^i K_0 (A)=Coker (N^i U(A_1) plus.o N^i U(A_2)
      -> N^i U(A'))$ для $i > 0$.]
  <cond:quasiregular-commutative-nil-k-zero-cokernel>
] <prop:quasiregular-pullback-k-groups>

#proof[
  Пусть $F=N^i K_j$, где $i >= 0$ и $j=0$ или 1. Тогда получаем (см. теорему
  @th:long-k-mayer-vietoris) последовательность Майера — Вьеториса
  $
    dots L^(n-1) F(A_1) plus.o L^(n-1) F(A_2) -> L^(n-1) F(A')
    -> L^n F(A) -> L^n F(A_1) plus.o L^n F(A_2) dots
  $
  При $j=0$, если $n > 1$ или если $n > 0$ и $i > 0$, то из предложения
  @prop:quasiregular-k-functor-vanishing следует, что все члены
  последовательности, окружающие группу $L^n F(A)=L^n N^i K_0 (A)$, равны нулю.
  Следовательно, и указанная группа также равна нулю. Это доказывает п.
  @cond:quasiregular-pullback-k-vanishing. Аналогично получаем утверждение
  @cond:quasiregular-pullback-contracted-k-zero из рассмотрения точной
  последовательности и предложения @prop:quasiregular-k-functor-vanishing при
  $n=1$ и $i=0=j$. Этим же методом получим утверждение
  @cond:quasiregular-nil-k-zero-cokernel при $n=1=j$ (учитывая, что
  $L N^i K_1=N^i L K_1=N^i K_0$). Наконец, эквивалентность условий
  @cond:quasiregular-commutative-nil-k-zero-cokernel и
  @cond:quasiregular-nil-k-zero-cokernel в коммутативном случае следует опять же
  из @prop:quasiregular-k-functor-vanishing, что и требовалось доказать.
]

#corollary[
  В ситуации предложения @prop:quasiregular-pullback-k-groups оказывается, что
  для всех $n >= 1$
  $ K_0 (A[T^n])=(1+2N)^n K_0 (A) plus.o n L K_0 (A) $
  и
  $
    K_1 (A[T^n])=(1+2N)^n K_1 (A) plus.o n K_0 (A)
    plus.o (n(n-1))/2 L K_0 (A).
  $
] <cor:quasiregular-pullback-laurent-k-groups>

#proof[
  Если $F=K_0$ или $K_1$, то $F(A[T^n])=(1+2N+L)^n F(A)$ (см.
  @cor:contracted-functor-abelian-extensions). Тогда
  $
    (1+2N+L)^n=(1+2N)^n+n(1+2N)^(n-1) L
    +(n(n-1))/2 (1+2N)^(n-2) L^2+dots.
  $
  Все кратные функторов $N L$ или $L^2$ аннулируют функтор $K_0=L K_1$, и все
  кратные функторов $N L^2$ или $L^3$ аннулируют функтор $K_1$ (это следует из
  @prop:quasiregular-pullback-k-groups). Следствие немедленно вытекает из этих
  замечаний.
]

#source(523)Предложение @prop:quasiregular-pullback-k-groups и его следствие в
основном применяются в такой ситуации. Пусть $R$ — дедекиндово кольцо с полем
частных $L$, $A$ есть $R$-порядок в полупростой $L$-алгебре, $A_2$ —
максимальный порядок, содержащий $A$, и $frak(c)=frak(c)_(A_2/A)$ — кондуктор.
Положим $A_1=A/frak(c)$ и $A'=A_2/frak(c)$. Эти кольца артиновы и,
следовательно, квазирегулярны. Кроме того, кольцо $A_2$ наследственно и, значит,
также квазирегулярно (на самом деле регулярно). Если $A=R pi$ (т. е. $A$ —
групповое кольцо) и при этом порядок конечной группы $pi$ не делится на
$char(L)$, то $A[T^n]=R[pi times T^n]$. Поэтому можно применять
@cor:quasiregular-pullback-laurent-k-groups для сведения вычисления групп
$K_j (R[pi times T^n])$ к случаю кольца $R pi$.

#theorem[
  Пусть $A$ — коммутативное нётерово кольцо, размерность которого $<= 1$, и
  пусть $nil(A)=0$. Допустим, что целое замыкание $B$ кольца $A$ в его полном
  кольце частных является конечно порожденным $A$-модулем. Пусть
  $frak(c)=frak(c)_(B/A)$ — кондуктор. Положим $A'=A/frak(c)$ и $B'=B/frak(c)$.
  Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[отображение
      $det_0 (A[T^n]): Rk_0 (A[T^n]) -> Pic(A[T^n])$ является изоморфизмом для
      всех $n >= 0$, и аналогичное утверждение имеет место для отображения
      $det_0 (A[T_+^n])$;] <cond:polynomial-determinant-isomorphism>
    #condition-item(format: "cyrillic")[
      $ K_0 (A[T^n])=(1+2N)^n K_0 (A) plus.o n L K_0 (A) $
      и
      $
        K_1 (A[T^n])=(1+2N)^n K_1 (A) plus.o n K_0 (A)
        plus.o (n(n-1))/2 L K_0 (A);
      $
    ] <cond:conductor-laurent-k-decomposition>
    #condition-item(format: "cyrillic")[группа $L K_0 (A)$ изоморфна группе
      $ Coker (H_0 (A') plus.o H_0 (B) -> H_0 (B')), $
      которая является свободной абелевой группой ранга
      $h_0 (A)-(h_0 (A')+h_0 (B))+h_0 (B')$;]
    <cond:conductor-contracted-k-zero-rank>
    #condition-item(format: "cyrillic")[если $G=T_+^n$, то
      $
        Ker(K_0 (A[G]) -> K_0 (A)) approx ((1+N)^n-1)K_0 (A)
        approx (1+nil(B')overline(B'[G]))/(1+nil(A')overline(A'[G])),
      $
      причем при $n > 0$ эта группа равна нулю тогда и только тогда, когда
      $nil(B')=0$. Степени идеала $nil(B')$ индуцируют конечную фильтрацию на
      этой группе, а факторы этой фильтрации оказываются изоморфными
      фактормодулям $A'$-модуля $overline((B'/nil(B'))[G])$.]
    <cond:conductor-nil-k-zero-filtration>
  ]
] <th:polynomial-determinant-isomorphism>

#proof[
  Из предположений следует, что $B$ — конечное произведение дедекиндовых колец и
  что $A'$ и $B'$ — артиновы кольца. Следовательно, эти три кольца являются
  квазирегулярными. Поэтому утверждение @cond:conductor-laurent-k-decomposition
  следует из @cor:quasiregular-pullback-laurent-k-groups.

  @cond:polynomial-determinant-isomorphism Пусть $G=T^n$ или $G=T_+^n$. Чтобы
  показать, что отображение $det_0 (A[G])$ — изоморфизм, достаточно (в силу
  @cor:milnor-determinant-isomorphism) показать, что:
  #condition-list[
    #condition-item[#source(524)отображения $det_0 (A'[G])$ и $det_0 (B[G])$ —
      изоморфизмы;] <cond:conductor-picard-base-isomorphisms>
    #condition-item[отображение $det_1 (B'[G])$ — изоморфизм.]
    <cond:conductor-unit-determinant-isomorphism>
  ]
  Так как кольца $A'$ и $B$ квазирегулярны, то из теоремы Серра
  @th:regular-polynomial-k-zero вытекает, что отображения $det_0 (B[G])$ и
  $det_0 (B)$ изоморфны и что аналогичное утверждение справедливо для кольца
  $A'$. Так как размерности колец $A'$ и $B$ не превосходят 1, то из
  @prop:reduced-determinant-stable-characterization следует, что отображения
  $det_0 (A')$ и $det_0 (B)$ являются изоморфизмами. Это доказывает
  @cond:conductor-picard-base-isomorphisms.

  Часть @cond:conductor-unit-determinant-isomorphism утверждает, что
  $SK_1 (B'[G])=0$. Но $SK_1 (B'[G])=P SK_1 (B')$, где $P=(1+N)^n$, если
  $G=T_+^n$, и $P=(1+2N)^n+n L+(n(n-1))/2 L^2$, если $G=T^n$ (последняя формула
  вытекает из следствия @cor:quasiregular-pullback-laurent-k-groups). Из
  @prop:quasiregular-k-functor-vanishing следует, что $N^i SK_1 (B')=0$ для
  $i > 0$, и $SK_1 (B')=0$, поскольку кольцо $B'$ артиново. По той же причине
  $L SK_1 (B')=Rk_0 (B')=0$. Наконец, из @prop:quasiregular-k-functor-vanishing
  следует, что $L^2 K_1 (B')=L K_0 (B')=0$. Поэтому также $L^2 SK_1 (B')=0$. Это
  доказывает @cond:conductor-unit-determinant-isomorphism и, следовательно,
  утверждение @cond:polynomial-determinant-isomorphism.

  @cond:conductor-contracted-k-zero-rank Из утверждения
  @prop:quasiregular-pullback-k-groups
  @cond:quasiregular-pullback-contracted-k-zero следует, что
  $ L K_0 (A) approx Coker (K_0 (A') plus.o K_0 (B) -> K_0 (B')). $
  Так как кольцо $B'$ артиново, то отображение $K_0 (B') -> H_0 (B')$ —
  изоморфизм. Поэтому коядро не меняется при замене всюду $K_0$ на $H_0$. Таким
  образом, из @prop:milnor-spectrum-rank-pushout получаем существование точной
  последовательности
  $ 0 -> H_0 (A) -> H_0 (A') plus.o H_0 (B) -> H_0 (B') -> L K_0 (A) -> 0, $
  а также и тот факт, что группа $L K_0 (A)$ без кручения и, следовательно,
  является свободной абелевой группой ранга
  $h_0 (A)-(h_0 (A')+h_0 (B))+h_0 (B')$.

  @cond:conductor-nil-k-zero-filtration Пусть $G=T_+^n$. Рассмотрим морфизм
  последовательностей Майера — Вьеториса.
  #conductor-k-augmentation-square()
  Правое вертикальное отображение — изоморфизм, поскольку кольца $A'$ и $B$
  квазирегулярны. Кроме того, левое отображение изоморфно отображению
  $U(B'[G]) -> U(B')$ (учитывая отображение $det_1$). Рассматривая ядра
  вертикальных отображений, получаем, что
  $
    Ker(K_0 (A[G]) -> K_0 (A))=((1+N)^n-1)K_0 (A)
    approx Coker (U(A'[G],overline(A'[G])) plus.o U(B[G],overline(B[G]))
      -> U(B'[G],overline(B'[G]))).
  $
  #source(525)Однако из @prop:unit-functor-contraction легко следует, что
  $U(C[G],overline(C[G]))=1+nil(C)times overline(C[G])$ для любого
  коммутативного кольца $C$. Так как $nil(B)=0$, то приведенная выше группа
  равна
  $ (1+nil(B')overline(B'[G]))/(1+nil(A')overline(A'[G])). $
  Пусть $frak(b)_i=nil(B')^i dot overline(B'[G])$ $(i >= 1)$. Тогда $frak(b)_i$
  — нильпотентный идеал кольца $B'[G]$. Так как
  $frak(b)_i^2 subset frak(b)_(2i) subset frak(b)_(i+1)$, то мы видим, что в
  группе $U(B'[G]/frak(b)_(i+1))$ подгруппа $1+(frak(b)_i/frak(b)_(i+1))$
  изоморфна аддитивной группе
  $
    frak(b)_i/frak(b)_(i+1) approx (nil(B')^i/nil(B')^(i+1))
    tensor_(B') overline(B'[G]),
  $
  которая является фактормодулем
  $ (B'/nil(B')) tensor_(B') overline(B'[G]) approx overline((B'/nil(B'))[G]). $
  Таким образом, в силу указанного изоморфизма рассмотрение факторов образа
  группы $(1+nil(A')overline(A'[G])) inter (1+frak(b)_i)$ в группе
  $1+(frak(b)_i/frak(b)_(i+1))$ приводит к рассмотрению факторов $A'$-подмодуля
  модуля $overline((B'/nil(B'))[G])$. Это доказывает последнее утверждение части
  @cond:conductor-nil-k-zero-filtration.

  Очевидно, что рассмотренная группа равна нулю тогда и только тогда, когда
  $nil(A')overline(A'[G])=nil(B')overline(B'[G])$. Очевидно, что это условие
  выполнено, если $nil(B')=0$. Обратно, из равенства
  $nil(A')overline(A'[G])=nil(B')overline(B'[G])$ следует, что
  $nil(B') subset A'$, т. е. что $root(B, frak(c)) subset A$. Так как кондуктор
  $frak(c)$ — это наибольший $B$-идеал в $A$, то $frak(c)=root(B, frak(c))$, т.
  е. $nil(B')=0$.

  Это завершает доказательство @cond:conductor-nil-k-zero-filtration и,
  следовательно, теоремы @th:polynomial-determinant-isomorphism.
]

#example[
  Пусть $k$ — поле и $A=k[s^2,s^3] subset B=k[s]$, где $s$ — переменная. Тогда
  $frak(c)=s^2 B$. Поэтому $A'=k$ и $B'=k[s']$, $(s')^2=0$. Следовательно,
  $
    K_0 (A[t]) approx K_0 (A) plus.o (1+s'(t-1)B'[t])
    approx K_0 (A) plus.o k[t].
  $
  Таким образом, группа $K_0 (A[t])$ содержит бесконечномерное векторное
  пространство над полем $k$.
] <exm:cusp-polynomial-picard>

#theorem[
  Пусть $pi$ — конечная абелева группа порядка $m=[pi:1]$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[Отображение
      $det_0 (ZZ[pi times T^n]):
      Rk_0 (ZZ[pi times T^n]) -> Pic(ZZ[pi times T^n])$
      является изоморфизмом для всех $n >= 0$.]
    <cond:abelian-group-ring-laurent-determinant>
    #condition-item(format: "cyrillic")[
      $ K_0 (ZZ[pi times T^n])=(1+2N)^n K_0 (ZZ pi) plus.o n L K_0 (ZZ pi) $
      и
      $
        K_1 (ZZ[pi times T^n])=(1+2N)^n K_1 (ZZ pi) plus.o n K_0 (ZZ pi)
        plus.o (n(n-1))/2 L K_0 (ZZ pi).
      $
    ] <cond:abelian-group-ring-laurent-k-decomposition>
    #condition-item(format: "cyrillic")[$L K_0 (ZZ pi)$ — свободная абелева
      группа ранга
      $ (1-h_0 (QQ pi))+sum_(p divides m) h_0 (FF_p pi'_p)(h_0 (QQ pi_p)-1), $
      где $FF_p=ZZ/(p ZZ)$, $pi_p$ — силовская $p$-под#source(526)группа группы
      $pi$ и $pi=pi_p times pi'_p$ для каждого простого числа $p$. Эта группа
      равна нулю тогда и только тогда, когда число $m$ является степенью
      простого числа.] <cond:abelian-group-ring-negative-k-zero-rank>
    #condition-item(format: "cyrillic")[Если число $m$ не содержит квадратов
      (тогда $pi$ — циклическая группа), то $N^i K_0 (ZZ pi)=0$ для всех
      $i > 0$. В противном случае найдется число $d > 0$ такое, что для всех
      $i > 0$ группа $N^i K_0 (ZZ pi)$ является бесконечной группой экспоненты
      $m^d$. Для любой группы $pi'$ группа $N K_0 (ZZ pi')$ является прямым
      слагаемым в группе $NilGroup (ZZ[pi' times T])$.]
    <cond:abelian-group-ring-nil-k-zero-infinitude>
    #condition-item(format: "cyrillic")[Порядок каждого элемента группы
      $NilGroup (ZZ[pi times T^n])$ делит некоторую степень числа $m$. Это же
      утверждение верно и для группы $N^i K_1 (ZZ pi)$ при всех $i > 0$.]
    <cond:abelian-group-ring-nil-k-one-torsion>
  ]
] <th:finite-abelian-group-ring-polynomial-k-groups>

#proof[
  Пусть $A=ZZ pi$, а $B$ и $frak(c)$ выбраны так же, как в
  @th:polynomial-determinant-isomorphism. Предположения теоремы
  @th:polynomial-determinant-isomorphism в нашем случае выполнены. Поэтому
  утверждения @cond:abelian-group-ring-laurent-determinant и
  @cond:abelian-group-ring-laurent-k-decomposition следуют непосредственно из
  соответствующих утверждений @cond:polynomial-determinant-isomorphism и
  @cond:conductor-laurent-k-decomposition теоремы
  @th:polynomial-determinant-isomorphism. Часть
  @cond:abelian-group-ring-negative-k-zero-rank следует из части
  @cond:conductor-contracted-k-zero-rank теоремы
  @th:polynomial-determinant-isomorphism и
  @prop:abelian-group-conductor-component-ranks. Так как $m B subset frak(c)$
  (см. @th:maschke), то характеристика кольца $B'=B/frak(c)$ делит число $m$.
  Поэтому из @th:polynomial-determinant-isomorphism
  @cond:conductor-nil-k-zero-filtration вытекает, что если $nil(B')^(d+1)=0$, то
  экспонента группы $N^i K_0 (ZZ pi)$ равна $m^d$ для всех $i > 0$. Кроме того,
  все эти группы равны нулю, если $frak(c)=root(B, frak(c))$. Из
  @cor:cyclotomic-group-ring-conductor вытекает, что это выполняется тогда и
  только тогда, когда число $m$ не содержит квадратов.

  Далее, из утверждения @th:polynomial-determinant-isomorphism
  @cond:conductor-nil-k-zero-filtration получим, что
  $
    Ker(K_0 (ZZ[pi times T_+^n]) -> K_0 (ZZ pi))
    approx ((1+N)^n-1)K_0 (ZZ pi)
    approx (1+nil(B')overline(B'[T_+^n]))/(1+nil(A')overline(A'[T_+^n])),
  $
  где $A'=A/frak(c)$. Покажем, что если $nil(B') != 0$ и, таким образом,
  $nil(A') != nil(B')$, то эта группа бесконечна (для $n > 0$). Приведем
  доказательство для $n=1$ и оставим общий случай читателю.

  Пусть $s=t-1$, где элемент $t$ порождает $T_+$. Если бы рассмотренная выше
  группа была конечной, то существовало бы число $n_0 > 0$, для которого каждый
  элемент группы представляется в виде многочлена от $s$ степени $< n_0$. Но
  если $b in nil(B')$, $b in.not nil(A')$ и степень многочлена $P(s) in B'[s]$
  строго меньше числа $n_0$, то коэффициент с номером $n_0$ многочлена
  $P(s)(1+b s^(n_0))$ равен $b$. Таким образом, элемент $(1+b s^(n_0))$ не может
  быть представлен по модулю $1+nil(A')overline(A'[T_+])$ в виде многочлена
  степени $< n_0$.

  Для завершения доказательства утверждения
  @cond:abelian-group-ring-nil-k-zero-infinitude отметим, что
  $N K_0 (A)=N L K_1 (A)=L N K_1 (A)=L NilGroup (A)$ для любого кольца $A$, при
  этом в силу основной теоремы @th:fundamental-k-theory-laurent последняя группа
  является прямым слагаемым группы $NilGroup (A[T])$.

  #source(527)Утверждение @cond:abelian-group-ring-nil-k-one-torsion вытекает из
  @prop:subdirect-polynomial-k-one-torsion, если учесть, что $m B subset A$ и
  что $A$ проектируется на каждый сомножитель кольца $B$, а все они являются
  дедекиндовыми кольцами. Последнее утверждение вытекает из первого, так как
  $N K_1=NilGroup$ и, следовательно,
  $
    NilGroup (ZZ[pi times T^n])=(1+2N+L)^n NilGroup (ZZ pi)
    =(1+2N+L)^n N K_1 (ZZ pi).
  $
  Это завершает доказательство теоремы
  @th:finite-abelian-group-ring-polynomial-k-groups.
]
