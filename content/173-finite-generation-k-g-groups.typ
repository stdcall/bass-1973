#import "main-defs.typ": (
  Coker, E, End, G, GL, Im, K, Ker, Nrd, SK, SL, SR, U, det, ed-note, idx,
  name-idx, rad, source, symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, hypothesis, proof, proposition,
  theorem,
)
#import "diagrams/arithmetic-finiteness-cartan.typ": (
  diagram-cartan-k1-order-comparison,
)

#heading(level: 2)[Конечная порождаемость групп $K_1$ и $G_1$]
<sec:finite-generation-k-g-groups>

Сохраним обозначения и соглашения @eq:arithmetic-finiteness-data и
@eq:arithmetic-base-data из § @sec:finiteness-of-class-number и добавим к ним
следующее:

$
           C & — "центр алгебры" Lambda; \
          R' & — "целое замыкание кольца" R "в" C; \
  L_infinity & = cases(
                 RR & "если" R=ZZ,
                 F((t^(-1))) & "если" R=F[t]
               ).
$ <eq:arithmetic-center-data>
#symbol-idx($L_infinity$, sort: "L_∞", group: "groups", order: 109)

Далее будем считать, что $C$ — сепарабелен над $L$. Отсюда следует, что
$L_infinity$-алгебра $Lambda_infinity=Lambda tensor_L L_infinity$ полупроста, а
ее центр совпадает с $C_infinity=C tensor_L L_infinity$.

Сформулируем сначала две классические теоремы конечности.

#idx("теорема", "Дирихле")
#theorem(title: [Дирихле])[
  Абелева группа $U(R')$ конечно порождена, и ее ранг равен $r_infinity-r_0$,
  где

  $r_0$ — число простых факторов центра $C$ (или $Lambda$),

  $r_infinity$ — число простых факторов центра $C_infinity$ (или
  $Lambda_infinity$).
] <th:dirichlet-units>

Эту теорему можно найти почти в любой книге по теории чисел. Так как группа
$U(R')$ — прямое произведение своих проекций в простые факторы центра $C$, можно
задачу свести к случаю, когда $C$ — поле, т. е. когда $r_0=1$. Если $R=ZZ$, то
$C_infinity=RR^(r_1) times CC^(r_2)$, где $r_1+2 r_2=[C:QQ]$ и ранг группы
$U(R')$ равен $r_1+r_2-1$.

#idx("теорема", "Зигеля")
#name-idx("Борель (Borel A.)")
#name-idx("Хариш-Чандра (Harish-Chandra)")
#theorem(title: [Зигель @bib:Siegel1943; см. также Борель, Хариш-Чандра
  @bib:Borel1962])[
  Допустим, что $R=ZZ$. Тогда группа $SL_n (A)$ (и, следовательно, группа
  $GL_n (A)$) конечно порождена для всех $n>=1$.
] <th:siegel-arithmetic-linear-finite-generation>

Здесь под группой $SL_n (A)$ понимается ядро отображения

$ det (=Nrd_(Lambda slash C)): GL_n (A)->U(C) $

#source(420)
(см. гл. @ch:rings-modules, § @sec:orders-semisimple-algebras или гл.
@ch:stable-linear-groups, § @sec:semilocal-linear-groups, где рассматривалась
редуцированная норма). Так как элементы кольца $M_n (A)$ являются целыми над
$R$, то $det (alpha) in R'$ для $alpha in M_n (A)$ (см.
@eq:reduced-trace-integrality из гл. @ch:rings-modules, §
@sec:orders-semisimple-algebras). Таким образом, для каждого двустороннего
идеала $frak(q)$ кольца $A$ последовательность групп

$ 1 -> SL_n (A,frak(q)) -> GL_n (A,frak(q)) arrow^det U(R') $

точна (здесь, как обычно, $SL_n (A,frak(q))=GL_n (A,frak(q)) inter SL_n (A)$). В
силу теоремы @th:dirichlet-units мы понимаем, почему группа $GL_n (A)$ конечно
порождена, если конечно порождена группа $SL_n (A)$.

В функциональном случае аналог теоремы
@th:siegel-arithmetic-linear-finite-generation не всегда имеет место.
Действительно, группа $SL_2 (F[t])$ не является конечно порожденной. С другой
стороны, О'Мира показал, что группа $SL_n (R')$ конечно порождена при всех
$n>=3$. Даже более того, из @cor:arithmetic-special-linear-elementary и
@cor:finite-field-special-linear-elementary следует

#proposition[
  Для всех $n>=3$ имеет место равенство $SL_n (R')=E_n (R')$, и эта группа
  конечно порождена.
] <prop:arithmetic-integral-special-linear-generation>

#hypothesis(word: "Гипотеза")[
  Для всех $n>=3$ группа $SL_n (A)$ конечно порождена.
] <ss:arithmetic-order-special-linear-finite-generation>

В случае числовых полей это действительно так по теореме Зигеля.

Основная теорема этого параграфа —

#theorem[
  Пусть $frak(q)$ — двусторонний идеал кольца $A$ и

  $ SK_1 (A,frak(q))=SL(A, frak(q)) slash E(A,frak(q)), $

  так что можно рассмотреть точную последовательность

  $ 0 -> SK_1 (A,frak(q)) -> K_1 (A,frak(q)) arrow^det U(R'). $
  <eq:arithmetic-relative-determinant-sequence>

  Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[$SK_1 (A,frak(q))$ — периодическая
      группа ограниченной экспоненты. Если группа $GL_n (A)$ конечно порождена
      для некоторого $n>=2$, то группа $SK_1 (A,frak(q))$ конечна.]
    <cond:arithmetic-sk1-bounded-torsion>
    #condition-item(format: "cyrillic")[Если кольцо $A slash frak(q)$ конечно,
      то коядро отображения $det$ в @eq:arithmetic-relative-determinant-sequence
      конечно, и поэтому факторгруппа группы $K_1 (A,frak(q))$ по периодической
      подгруппе оказывается свободной абелевой группой ранга $r_infinity-r_0$ (в
      обозначениях теоремы @th:dirichlet-units). Если группа $SK_1 (A,frak(q))$
      конечна, то группы $GL_n (A)$ и $SL_n (A)$ конечно порождены при всех
      $n>=3$.]
    <cond:arithmetic-relative-k1-free-rank>
    #condition-item(format: "cyrillic")[Коядро гомоморфизма Картана
      $c_1(A):K_1(A)->G_1(A)$
      конечно.] <cond:arithmetic-cartan-k1-cokernel-finite>
  ]
] <th:arithmetic-k1-finiteness>

#corollary[
  В числовом случае $(R=ZZ)$ последовательность

  $ 0 -> SK_1 (A,frak(q)) -> K_1 (A,frak(q)) -> K_1 (Lambda) $

  #source(421)
  точна для всех идеалов $frak(q)$. Кроме того, группа $SK_1 (A,frak(q))$
  конечна, и поэтому группа $K_1 (A,frak(q))$ конечно порождена. Далее, группа
  $G_1(A)$ конечно порождена, а группа $Ker (G_1(A)->G_1(Lambda))$ конечна.
] <cor:number-order-k1-g1-finite-generation>

#proof[
  Первое утверждение следует из теоремы Уонга @th:wang-reduced-whitehead-group.
  Конечность группы $SK_1 (A,frak(q))$ следует из @th:arithmetic-k1-finiteness
  @cond:arithmetic-sk1-bounded-torsion и теоремы Зигеля
  @th:siegel-arithmetic-linear-finite-generation. Коядро гомоморфизма

  $ Ker (K_1(A)->K_1(Lambda))=SK_1(A)->Ker (G_1(A)->G_1(Lambda)) $

  конечно в силу @th:arithmetic-k1-finiteness
  @cond:arithmetic-cartan-k1-cokernel-finite. Образы групп $K_1(A,frak(q))$ и
  $G_1(A)$ в $K_1(Lambda)$ отождествляются при помощи отображения $det$ с
  подгруппами конечно порожденной группы $U(R')$, и поэтому они также конечно
  порождены, что и требовалось доказать.
]

#proof(head: [Доказательство теоремы @th:arithmetic-k1-finiteness.])[
  Проведем в несколько шагов.
  #condition-list[
    #condition-item(format: "degree")[_Если $frak(q)$ — двусторонний идеал
      кольца $A$, то существует другой идеал $frak(q)'$, такой, что
      $frak(q) inter frak(q)'=0$ и кольцо $A slash (frak(q)+frak(q)')$ конечно.
      Кроме того,_

      $ K_1(A,frak(q)+frak(q)')=K_1(A,frak(q)) plus.o K_1(A,frak(q)'), $

      $ SK_1(A,frak(q)+frak(q)')=SK_1(A,frak(q)) plus.o SK_1(A,frak(q)'). $

      Действительно, $frak(q) tensor_R L$ — двусторонний идеал в полупростой
      алгебре $Lambda$. Пусть $frak(q)' subset A$ — двусторонняя $A$-решетка в
      дополнительном двустороннем идеале. Тогда $frak(q) inter frak(q)'=0$ и
      $frak(q)+frak(q)'$ является $R$-решеткой в $Lambda$. Следовательно, кольцо
      $A slash (frak(q)+frak(q)')$ конечно. Остальные утверждения вытекают из
      @prop:disjoint-ideal-relative-k-decomposition и покоординатного
      определения редуцированной нормы.]
    <cond:arithmetic-ideal-complement-reduction>
  ]

  Допустим, что кольцо $A slash frak(q)$ конечно. Пусть $B$ — максимальный
  $R$-порядок, содержащий $A$. Выберем ненулевой элемент $a$ кольца $R$ так,
  чтобы $a B subset frak(q)$.

  #condition-list(start: 2)[
    #condition-item(format: "degree")[_Коядро гомоморфизма_

      $ K_1(A,frak(q))->K_1(B) $

      _конечно. Существует гомоморфизм_

      $ SK_1(B,a^2 B)->SK_1(A,frak(q)), $

      _коядро которого также конечно._

      Заметим, что $GL_n (A,a B)=GL_n (B,a B)$, так как обе группы состоят из
      таких матриц $alpha in GL_n (Lambda)$, для которых координаты матриц
      $I-alpha$ и $I-alpha^(-1)$ лежат в $a B$. Так как кольцо $B slash a B$
      конечно, то индекс подгруппы $GL_n (B,a B)$ в группе $GL_n (B)$ конечен.
      Следовательно (так как $GL_n (A,a B) subset GL_n (A,frak(q))$), индекс
      последней подгруппы в $GL_n (B)$ конечен. Из этого замечания при $n>=2$
      следует первое утверждение.

      #source(422)
      Далее, отметим, что при $n>=3$

      $
        E_n (A,frak(q)) supset E_n (A,a B)
        supset [GL_n (A,a B),GL_n (A,a B)]
        = [GL_n (B,a B),GL_n (B,a B)] supset E_n (B,a^2 B)
      $

      (см. @cor:stable-linear-relative-commutators и
      @cor:linear-stability-dimension-bound для первого включения коммутатора и
      @cor:relative-elementary-commutators для последнего). Очевидно, что также
      $SL_n (B,a^2 B)=SL_n (A,a^2 B)
      subset SL_n (A,frak(q))$. Поэтому получаем гомоморфизм
      $SK_1(B,a^2 B)->SK_1(A,frak(q))$, индуцированный вложениями. Как и выше,
      убеждаемся, что коядро этого гомоморфизма конечно, поскольку индекс
      подгруппы $SL_n (B,a^2 B)$ в группе $SL_n (B)$ конечен.]
    <cond:arithmetic-maximal-order-sk1-comparison>
    #condition-item(format: "degree")[_Коядро отображения
      $det:K_1(A,frak(q))->U(R')$ конечно._

      Учитывая @cond:arithmetic-maximal-order-sk1-comparison, достаточно
      показать, что коядро отображения $det:K_1(B)->U(R')$ конечно. Так как $B$
      — произведение максимальных порядков в простых сомножителях алгебры
      $Lambda$, то можно считать, что алгебра $Lambda$ простая. Пусть
      $[Lambda:C]=n^2$. Тогда если $a in U(R')$, то
      $Nrd_(Lambda slash C) (a)=a^n$ (см. гл. @ch:rings-modules, §
      @sec:orders-semisimple-algebras). Так как $R' subset B$, то $det (K_1(B))$
      содержит все $n$-е степени элементов группы $U(R')$. В силу
      @th:dirichlet-units группа $U(R')$ конечно порождена. Отсюда следует
      нужное утверждение.]
    <cond:arithmetic-determinant-cokernel-finite>
    #condition-item(format: "degree")[_При любом двустороннем идеале $frak(q)$
      кольца $A$ группа $SK_1(A,frak(q))$ является периодической группой
      ограниченной экспоненты._

      Учитывая @cond:arithmetic-ideal-complement-reduction, можем не теряя
      общности считать, что кольцо $A slash frak(q)$ конечно. Поэтому можно
      заменить пару $(A,frak(q))$ на $(B,a^2 B)$ (как в
      @cond:arithmetic-maximal-order-sk1-comparison) и считать далее, что $A$ —
      максимальный порядок. Тогда $A$ разлагается в произведение максимальных
      порядков в сомножителях алгебры $Lambda$, и идеал $frak(q)$ разлагается
      соответственно. Поэтому можно считать, что алгебра $Lambda$ простая. Пусть
      $C_1$ — конечное расширение центра $C$; при этом
      $Lambda tensor_C C_1 tilde.eq M_n (C_1)$. Пусть $R_1$ — целое замыкание
      кольца $R'$ в $C_1$. Положим $A_1=A tensor_(R') R_1$ и
      $frak(q)_1=frak(q) tensor_(R') R_1$. Тогда существует естественный
      гомоморфизм

      $ f:SK_1(A,frak(q))->SK_1(A_1,frak(q)_1), $

      поскольку редуцированная норма не меняется при замене базы. Кроме того, из
      @cor:projective-k-torsion-kernels следует, что подгруппа $Ker (f)$
      аннулируется числом $[R_1:R]^2$. Следовательно, доказательство будет
      завершено, если мы покажем, что группа $SK_1(A_1,frak(q)_1)$ конечна. (На
      этом пути лишь отсутствие контроля группой $Ker (f)$ не позволяет нам
      утверждать конечность группы $SK_1(A,frak(q))$. Таким образом, это
      рассуждение показывает, что группа $SK_1(A,frak(q))$ конечна, например, в
      том случае, когда алгебра $Lambda$ расщепляется.)

      Как и в случае пары $(A,frak(q))$, можем вложить $A_1$ в максимальный
      порядок $B_1$ и найти идеал $frak(b)_1$ кольца $B_1$, для которого кольцо
      #source(423)
      $B_1 slash frak(b)_1$ конечно и существует гомоморфизм
      $SK_1(B_1,frak(b)_1)->SK_1(A_1,frak(q)_1)$, коядро которого конечно. Так
      как $B_1$ — максимальный $R_1$-порядок в алгебре $M_n (C_1)$, то из
      @th:maximal-order-endomorphism-centralizer следует, что
      $B_1=End_(R_1) (P)$ для некоторого модуля $P in bold(italic(P)) (R_1)$.
      Теперь из развитой нами теории (гл. @ch:module-categories, §§
      @sec:module-equivalences—@sec:equivalence-from-module) следует, что
      $SK_1(B_1,frak(b)_1)=SK_1(R_1,frak(a))$ для некоторого ненулевого идеала
      $frak(a)$ кольца $R_1$. В случае функционального поля из
      @cor:finite-field-special-linear-elementary следует, что
      $SK_1(R_1,frak(a))=0$. Для числового поля из
      @th:bass-milnor-serre-reciprocity вытекает, что $SK_1(R_1,frak(a))$ —
      конечная циклическая группа, что и требовалось доказать.]
    <cond:arithmetic-sk1-splitting-field-reduction>
    #condition-item(format: "degree")[#emph[Доказательство утверждения
        @cond:arithmetic-sk1-bounded-torsion.]

      Первая часть утверждения вытекает из
      @cond:arithmetic-sk1-splitting-field-reduction. В силу
      @cond:arithmetic-ideal-complement-reduction можно считать, что кольцо
      $A slash frak(q)$ конечно. Тогда $GL_n (A,frak(q))$ имеет конечный индекс
      в конечно порожденной группе $GL_n (A)$ и потому конечно порождена. По
      @cor:linear-stability-dimension-bound выполнено условие $SR_3 (A)$;
      следовательно, из теоремы @th:linear-normal-subgroup-stability
      @cond:linear-relative-elementary-normality вытекает, что отображение
      $GL_n (A,frak(q))->K_1(A,frak(q))$ сюръективно для $n>=2$. Поэтому
      $K_1(A,frak(q))$ — конечно порожденная абелева группа, и ее подгруппа
      $SK_1(A,frak(q))$ также конечно порождена. Поскольку конечно порожденная
      периодическая абелева группа конечна, этим доказано
      @cond:arithmetic-sk1-bounded-torsion.#ed-note[
        В печатном доказательстве конечная порождаемость группы
        $SL_n (A,frak(q))$ используется без вывода из гипотезы о $GL_n (A)$.
        Вместо этого можно применить общий факт о конечной порождаемости
        подгруппы конечного индекса; см. #cite(<Loh2017>, form: "full"),
        следствие 4.2.14. Здесь индекс конечен, поскольку $GL_n (A,frak(q))$
        является ядром отображения в конечную группу $GL_n (A slash frak(q))$.
        Сюръективность на $K_1(A,frak(q))$ следует из теоремы
        @th:linear-normal-subgroup-stability
        @cond:linear-relative-elementary-normality, а конечная порождаемость ее
        подгруппы $SK_1(A,frak(q))$ — из абелевости $K_1$.
      ]]
    <cond:arithmetic-sk1-finite-generation-proof>
    #condition-item(format: "degree")[#emph[Доказательство утверждения
        @cond:arithmetic-relative-k1-free-rank.]

      Из @cond:arithmetic-determinant-cokernel-finite следует, что коядро
      отображения $det:K_1(A,frak(q))->U(R')$ конечно, а из
      @cond:arithmetic-sk1-splitting-field-reduction вытекает, что ядро этого
      отображения является периодической группой. Следовательно, факторгруппа
      группы $K_1(A,frak(q))$ по периодической подгруппе оказывается подгруппой
      конечного индекса в факторгруппе группы $U(R')$ по периодической
      подгруппе. В силу @th:dirichlet-units последняя группа является свободной
      абелевой группой ранга $r_infinity-r_0$. Отсюда и следует
      @cond:arithmetic-relative-k1-free-rank.]
    <cond:arithmetic-relative-k1-rank-proof>
    #condition-item(format: "degree")[#emph[Доказательство утверждения
        @cond:arithmetic-cartan-k1-cokernel-finite.]

      Пусть $B$ — максимальный порядок, содержащий $A$, и $frak(c)$ — кондуктор
      из $B$ в $A$. Пусть

      $ N=Im (G_1(A slash frak(c))->G_1(A)). $

      Рассмотрим (некоммутативную) диаграмму

      $ #diagram-cartan-k1-order-comparison() $
      <eq:arithmetic-cartan-k1-order-comparison>

      В силу @prop:abelian-k-pullback-generation $G_1(A)=Im (j)+N$, поскольку
      $A$ является расслоенным произведением $A slash frak(c)$ и $B$. Кроме
      того, так как кольцо $A slash frak(c)$ конечно, то группа
      $G_1(A slash frak(c)) (tilde.eq
        K_1((A slash frak(c)) slash rad (A slash frak(c))))$ конечна. Поэтому
      конечна группа $N$. Из части @cond:arithmetic-maximal-order-sk1-comparison
      следует, что коядро отображения $j$ конечно, а отображение $c_1(B)$ —
      изоморфизм (поскольку кольцо $B$ регулярно). Следовательно, утверждение
      @cond:arithmetic-cartan-k1-cokernel-finite о конечности коядра отображения
      $c_1(A)$ будет доказано, если мы убедимся в том, что диаграмма
      @eq:arithmetic-cartan-k1-order-comparison _коммутативна по модулю_ $N$.

      Пусть $(P,alpha) in Sigma bold(italic(P)) (A)$. Тогда, если
      $h=j^* c_1(B) j_*$, то $h[P,alpha]_(bold(italic(P))(A))=
      [P tensor_A B,alpha tensor_A B]_(bold(italic(M))(A))$. Домножив тензорно
      точную последовательность
      #source(424)
      двусторонних $A$-модулей

      $ 0 -> A -> B -> B slash A -> 0 $

      на $(P,alpha)$, увидим, что
      $[P tensor_A B,alpha tensor_A B]_(bold(italic(M))(A))=
      [P,alpha]_(bold(italic(M))(A))+
      [P tensor_A M,alpha tensor_A M]_(bold(italic(M))(A))$, где $M=B slash A$.
      Но $M frak(c)=0$. Поэтому второй член в правой части равенства лежит в
      $N$, что и требовалось доказать.]
    <cond:arithmetic-cartan-k1-cokernel-proof>
  ]
  Это завершает доказательство теоремы @th:arithmetic-k1-finiteness.
]

Закончим этот параграф частичным обобщением теоремы @th:arithmetic-k1-finiteness
для случая характеристики нуль.

#theorem[
  Пусть $B$ — любая конечномерная $ZZ$-алгебра. Тогда группа $GL_n (B)$ конечно
  порождена при всех $n>=1$. Кроме того, $K_1(B)$ и $G_1(B)$ — конечно
  порожденные абелевы группы.
] <th:finite-integral-algebra-linear-k1-g1-generation>

#proof[
  Как в @prop:finite-algebra-semisimple-order-reduction, существует максимальный
  нильпотентный двусторонний идеал $N$ в $B$, и $B slash N=A times T$, где $T$ —
  полупростое кольцо, а $A$ является $ZZ$-порядком в полупростой $QQ$-алгебре.
  Таким образом, получаем точную последовательность

  $ 1 -> U(B,N) -> U(B) -> U(B slash N) -> 1 $

  групп и разложение $U(B slash N)=U(A) times U(T)$. Группа $U(T)$ конечна, а
  группа $U(A)$ конечно порождена (в силу теоремы Зигеля
  @th:siegel-arithmetic-linear-finite-generation). По предложению
  @prop:nilpotent-units-finiteness, которое следует ниже, группа $U(B,N)$ также
  конечно порождена. Таким образом, группа $U(B)$ конечно порождена. Аналогично
  группа $U(M_n (B))=GL_n (B)$ конечно порождена при всех $n>=1$. Для $n>=2$
  отсюда следует, что $K_1(B)$ — конечно порожденная группа (см.
  @th:relative-k1-stability). Из @th:devissage-k-isomorphisms вытекает, что
  отображение

  $ G_1(B slash N)->G_1(B) $

  является изоморфизмом. Но $G_1(B slash N)=G_1(A) plus.o G_1(T)$, и группа
  $G_1(T)$ конечна. По @cor:number-order-k1-g1-finite-generation группа $G_1(A)$
  конечно порождена. Следовательно, конечно порождена и группа $G_1(B)$, что и
  требовалось доказать.
]

#proposition[
  Пусть $N$ — двусторонний идеал в кольце $B$. Предположим, что $N^(d+1)=0$ для
  некоторого $d>=0$. Пусть $G=1+N=U(B,N)$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[Если $d=1$, то отображение $N->G$
      $(a mapsto 1+a)$ является изоморфизмом групп.]
    <cond:square-zero-unit-additive-isomorphism>
    #condition-item(format: "cyrillic")[Если аддитивная группа $N$ конечно
      порождена, то $G$ — конечно порожденная группа.]
    <cond:nilpotent-unit-finite-generation>
    #condition-item(format: "cyrillic")[Если $e N=0$ для некоторого натурального
      числа $e>0$, то экспонента группы $G$ равна $e^d$, т. е. $x^(e^d)=1$ для
      всех $x in G$.] <cond:nilpotent-unit-exponent-bound>
  ]
] <prop:nilpotent-units-finiteness>

#source(425)
#proof[
  Утверждение @cond:square-zero-unit-additive-isomorphism очевидно.

  @cond:nilpotent-unit-finite-generation и @cond:nilpotent-unit-exponent-bound.
  Если $d=0$, то $N=0$ и утверждения очевидны. Далее пусть $d>=1$. Рассмотрим
  последовательность групп

  $ 1 -> 1+N^d -> 1+N -> 1+(N slash N^d) -> 1. $

  В силу @cond:square-zero-unit-additive-isomorphism ядро изоморфно группе $N^d$
  и, следовательно, конечно порождено (соответственно его экспонента равна $e$).
  Проводя индукцию по $d$, получаем, что факторгруппа конечно порождена
  (соответственно ее экспонента равна $e^(d-1)$). Следовательно, группа $1+N$
  конечно порождена (соответственно ее экспонента равна $e^d$).
]
