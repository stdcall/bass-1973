#import "main-defs.typ": (
  Aut, Coker, End, G, Im, InAut, K, Ker, Pic, U, alg, card, deg, det, divisor,
  idx, isoArrow, rank, source, symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition, theorem,
)
#import "diagrams/arithmetic-finiteness-cartan.typ": (
  diagram-cartan-class-number, diagram-cartan-kernels,
)

== Конечность числа классов <sec:finiteness-of-class-number>

До конца этой главы мы будем считать (уточняя предположения
@eq:arithmetic-finiteness-data из § @sec:swan-triangle-cartan-condition), что:

$
    F & — "конечное поле характеристики" p_0 "из" q=p_0^(n_0) "элементов;" \
    R & — "либо" ZZ, "либо" F[t], "где" t "— переменная;" \
  R_+ & = cases(
          {"целые" >= 0} & "если" R=ZZ,
          R & "если" R=F[t]
        ).
$ <eq:arithmetic-base-data>
#symbol-idx($R_+$, sort: "subscript +", group: "subscripts", order: 156)

Из @th:maximal-orders-existence следует, что каждый $R$-порядок в $Lambda$
является $R$-решеткой, причем его можно вложить в максимальный $R$-порядок.
#source(413)
Введем также гомоморфизм

$
  abs(dot): D(R) -> U(RR), quad
  abs(sum n_frak(p) frak(p)) = product abs(frak(p))^(n_frak(p))
  quad (frak(p) in X),
$

где $abs(frak(p))=card (R slash frak(p))$. Если $frak(a)$ — дробный идеал кольца
$R$, то положим

$ abs(frak(a))=abs(divisor (frak(a))), $
#symbol-idx($abs(frak(a))$, sort: "|a|", group: "symbols", order: 147)

и введем для краткости обозначение

$ abs(x)=abs(x R) quad (x in U(L)). $

Кроме того, будем считать, что $abs(0)=0$.

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[Если $frak(a)$ — ненулевой идеал кольца
      $R$, то

      $ abs(frak(a))=card (R slash frak(a)). $

      Следовательно, если $a in R$, то

      $
        abs(a)=cases(
          "обычное абсолютное значение" & "если" R=ZZ,
          q^(deg(a)) & "если" R=F[t]
        )
      $

      (по определению, $deg(0)=-infinity$).]
    <cond:arithmetic-absolute-value-cardinality>
    #condition-item(format: "cyrillic")[Если $a,b in R$, то

      $ abs(a+b)<=abs(a)+abs(b) $

      и

      $ abs(a-b)<=sup (abs(a),abs(b)) quad "для" a,b in R_+. $]
    <cond:arithmetic-absolute-value-triangle>
    #condition-item(format: "cyrillic")[Если $c$ — положительное вещественное
      число, то

      $ card {a in R bar abs(a)<=c}<infinity, $

      $ card {a in R_+ bar abs(a)<=c}>c. $]
    <cond:arithmetic-bounded-elements>
    #condition-item(format: "cyrillic")[Пусть
      $N(X_1,dots,X_m) in R[X_1,dots,X_m]$ — однородный многочлен степени $n$.
      Тогда существует вещественное число $c>0$, такое, что для всех
      $x=(x_1,dots,x_m) in R^m$

      $ abs(N(x))<=c abs(x)^n, $

      где $abs(x)=sup (abs(x_1),dots,abs(x_m))$.]
    <cond:arithmetic-polynomial-bound>
  ]
] <prop:arithmetic-absolute-value-properties>

#proof[
  @cond:arithmetic-absolute-value-cardinality Заметим, что
  $abs(frak(a))=abs(divisor (frak(a)))$ и $card (R slash frak(a))$ —
  мультипликативные функции от $frak(a)$, совпадающие на образующих
  $frak(a)=frak(p) in X$. Если $a != 0$ в $ZZ$, то ясно, что
  $card (ZZ slash a ZZ)$ — обычное абсолютное значение числа $a$. Если $a != 0$
  в $F[t]$ и $deg(a)=d$, то $R slash a R$ — векторное пространство над полем $F$
  с базисом $1,t,dots,t^(d-1)$. Следовательно, $card (R slash a R)=q^d$.

  @cond:arithmetic-absolute-value-triangle, @cond:arithmetic-bounded-elements
  Утверждение @cond:arithmetic-absolute-value-triangle немедленно вытекает из
  @cond:arithmetic-absolute-value-cardinality.
  #source(414)
  Это же можно сказать и о первой части утверждения
  @cond:arithmetic-bounded-elements. При $0<c<1$ множество
  ${a in R_+ bar abs(a)<=c}$ состоит из нуля. При $c>=1$ имеем

  $
    {a in R_+ bar abs(a)<=c} = cases(
      {0,1,dots,floor(c)} & "если" R=ZZ,
      sum_(0<=i<=floor(log_q c)) F t^i & "если" R=F[t]
    ).
  $

  Следовательно, число элементов равно соответственно $floor(c)+1$ и
  $q^(floor(log_q c)+1)$. Это доказывает вторую часть утверждения
  @cond:arithmetic-bounded-elements.

  @cond:arithmetic-polynomial-bound Пусть $N(x)=sum a_alpha x^alpha$, где
  $alpha=(i_1,dots,i_m)$ пробегает множество $m$-ок, таких, что $i_1+dots+i_m=n$
  и $x^alpha=x_1^(i_1) dots x_m^(i_m)$. Для каждой такой строчки $alpha$

  $
    abs(x^alpha)=abs(x_1)^(i_1) dots abs(x_m)^(i_m)
    <=abs(x)^(i_1) dots abs(x)^(i_m)=abs(x)^n.
  $

  Следовательно,

  $
    abs(N(x))<=sum abs(a_alpha) abs(x^alpha)
    <=sum abs(a_alpha) abs(x)^n<=c abs(x)^n,
  $

  где $c=sum abs(a_alpha)$, что и требовалось доказать.
]

Напомним, что если модуль $M in bold(italic(M)) (R)$ периодический, то

$ chi(M)=sum_(frak(p) in X) l_frak(p) (M) frak(p) in D(R), $

где $l_frak(p) (M)$ — длина $R_frak(p)$-модуля $M_frak(p)$ (см.
@prop:determinant-divisor-characteristic).

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[Если модуль $M in bold(italic(M)) (R)$
      периодический, то число $card (M)$ конечно и равно
      $abs(chi(M))$.] <cond:torsion-module-cardinality>
    #condition-item(format: "cyrillic")[Пусть определитель отображения
      $alpha:R^n->R^n$ отличен от нуля и $M=Coker (alpha)$. Тогда
      $M det(alpha)=0$ и

      $ card (M)=abs(det(alpha)). $] <cond:determinant-cokernel-cardinality>
    #condition-item(format: "cyrillic")[Пусть $c$ — положительное вещественное
      число. Через $W$ обозначим множество таких подмодулей $P subset R^n$, что
      $card (R^n slash P)<=c$. Тогда найдется элемент $d != 0$ в кольце $R$, для
      которого $R^n d subset P$ при всех $P in W$. Кроме того,
      $card (W)<infinity$.]
    <cond:bounded-index-lattices-finite>
  ]
] <prop:arithmetic-module-cardinality>

#proof[
  @cond:torsion-module-cardinality Модуль $M$ обладает композиционным рядом с
  факторами вида $R slash frak(p)$ $(frak(p) in X)$. Следовательно, $card (M)$ —
  конечное число. Так как
  $abs(chi(R slash frak(p)))=abs(frak(p))=card (R slash frak(p))$
  (в силу определения), то $card (M)=abs(chi(M))$ для всех рассматриваемых
  модулей $M$.

  Часть @cond:determinant-cokernel-cardinality непосредственно следует из
  @prop:determinant-divisor-characteristic с учетом части
  @cond:torsion-module-cardinality.

  @cond:bounded-index-lattices-finite Допустим, что $P in W$. Так как $R$ —
  кольцо главных идеалов, то модуль $P$ — свободный. Поэтому $P=Im (alpha)$ для
  некоторого эндоморфизма $alpha in End_R (R^n)$. Таким образом, в силу
  @cond:determinant-cokernel-cardinality
  $abs(det(alpha))=card (R^n slash P)<=c$. Пусть
  ${d_1,dots,d_m}={a in R bar 0<abs(a)<=c}$ (мы используем
  @prop:arithmetic-absolute-value-properties @cond:arithmetic-bounded-elements).
  Положим $d=d_1 dots d_m$. Так как $(R^n slash P) det(alpha)=0$, то
  $(R^n slash P) d=0$. Следовательно, $R^n supset P supset R^n d$. Поскольку
  множество $R^n slash R^n d=(R slash R d)^n$ конечно,
  #source(415)
  в множестве $W$ также конечное число различных модулей $P$, что и требовалось
  доказать.
]

Теперь вернемся к нашему обсуждению $R$-порядков, сохраняя в силе обозначения и
соглашения @eq:arithmetic-finiteness-data и @eq:arithmetic-base-data.

#proposition[
  Если $Lambda$ — тело, то число классов изоморфных правых $A$-идеалов конечно.
] <prop:division-order-ideal-classes-finite>

#proof[
  Если $frak(a) != 0$ — правый $A$-идеал, то $frak(a) L=Lambda$ (поскольку в
  $Lambda$ нет собственных правых идеалов). Таким образом, $frak(a)$ является
  $R$-решеткой в $Lambda$. Поэтому $c=card (A slash frak(a))$ — конечное число.

  Пусть $e_1,dots,e_n$ — $R$-базис в $A$. Положим

  $ W={sum_(1<=i<=n) e_i a_i bar a_i in R_+,abs(a_i)<=c^(1/n),1<=i<=n}. $

  В силу @prop:arithmetic-absolute-value-properties
  @cond:arithmetic-bounded-elements $card (W)>(c^(1/n))^n=c$. Следовательно,
  найдутся различные элементы $u$ и $v$ из $W$, для которых
  $u equiv v mod frak(a)$. Пусть $u=sum e_i a_i$ и $v=sum e_i b_i$. Тогда
  $w=u-v=sum e_i c_i != 0$, где

  $ abs(c_i)=abs(a_i-b_i)<=sup (abs(a_i),abs(b_i))<=c^(1/n) $

  (с учетом @prop:arithmetic-absolute-value-properties
  @cond:arithmetic-absolute-value-triangle). Кроме того, $w in frak(a)$,
  поскольку $u equiv v mod frak(a)$.

  Рассмотрим норму $N_(A slash R) (x)=det_R (A arrow^(x dot) A)$. Если
  $x=sum e_i x_i in A$, то $N_(A slash R) (x)$ — однородный многочлен степени
  $n$ от переменных $(x_1,dots,x_n)$ с коэффициентами из кольца $R$. Таким
  образом, если $abs(x)=sup (abs(x_1),dots,abs(x_n))$, то из
  @prop:arithmetic-absolute-value-properties
  @cond:arithmetic-polynomial-bound следует существование константы $K$
  (зависящей лишь от $A$), для которой $abs(N_(A slash R) (x))<=K abs(x)^n$ при
  всех $x in A$. Теперь опять из @prop:arithmetic-module-cardinality
  @cond:determinant-cokernel-cardinality следует, что

  $
    abs(N_(A slash R) (x))=card (Coker (A arrow^(x dot) A))
    =card (A slash x A),
  $

  если $N_(A slash R) (x) != 0$.

  Далее можно применить это рассуждение к построенному выше элементу $w != 0$.
  Так как $Lambda$ — алгебра с делением, то
  $N_(A slash R) (w)=N_(Lambda slash L) (w) != 0$ и, следовательно,
  $card (A slash w A)<=K abs(w)^n<=K(c^(1/n))^n=K c$. Так как $w in frak(a)$, то
  получаем точную последовательность

  $ 0 -> frak(a) slash w A -> A slash w A -> A slash frak(a) -> 0. $

  Поэтому $c(card (frak(a) slash w A))=card (A slash frak(a))
  card (frak(a) slash w A)=card (A slash w A)<=K c$. Следовательно,
  $card (frak(a) slash w A)<=K$. В силу @prop:arithmetic-module-cardinality
  @cond:bounded-index-lattices-finite найдется ненулевой элемент $d$ кольца $R$,
  зависящий лишь от $K$, для которого $(frak(a) slash w A) d=0$. Итак,
  $frak(a) d subset w A subset frak(a)$, т. е.
  $A subset w^(-1) frak(a) subset d^(-1) A$. Но правые идеалы $frak(a)$ и
  $w^(-1) frak(a)$ изоморфны; при этом $d$ зависит лишь от $K$ и, следовательно,
  лишь от $A$. Так как множество $d^(-1) A slash A$ конечно и так как мы
  показали, что $frak(a)$ изоморфен
  #source(416)
  некоторому правому идеалу между $A$ и $d^(-1) A$, то предложение доказано.
]

#idx("теорема", "Жордана — Цассенхауза")
#theorem(title: [Жордана — Цассенхауза])[
  Пусть $V in bold(italic(M)) (Lambda)$. Тогда число $c_A (V)$ классов
  изоморфных $A$-решеток в $V$ конечно.
] <th:jordan-zassenhaus>

Прежде чем доказать это, приведем сначала

#corollary[
  Если $n>0$, то существует лишь конечное число классов изоморфных модулей
  $M in bold(italic(M)) (A)$, являющихся $R$-модулями без кручения ранга $<=n$.
] <cor:bounded-rank-torsion-free-modules-finite>

#proof[
  Каждый такой модуль $M$ является $R$-решеткой в
  $V=M tensor_R L in bold(italic(M)) (Lambda)$ и $[V:L]<=n$. Так как алгебра
  $Lambda$ полупроста, то число таких $Lambda$-модулей $V$ (с точностью до
  изоморфизма) конечно. Поэтому следствие вытекает из теоремы.
]

#proof(head: [Доказательство теоремы @th:jordan-zassenhaus.])[
  Заметим, что кольцо $A$ можно вложить в максимальный порядок $B$ (см.
  @th:maximal-orders-existence). Выберем ненулевой элемент $a$ в кольце $R$ так,
  чтобы $B a subset A$. Если $M$ является $A$-решеткой в $V$, то $M B$ является
  $B$-решеткой и $M B a subset M subset M B$. Если $N$ — другая $A$-решетка и
  $M B tilde.eq N B$ (как $B$-решетки), то, применяя автоморфизм модуля $V$ к
  $N$, можно считать, что $M B=N B$. Тогда
  $M B a=N B a subset N subset N B=M B$. Таким образом, каждая $A$-решетка $N$,
  для которой $M B tilde.eq N B$ (как $B$-решетки), имеет представителя (из
  своего класса), зажатого между $M B a$ и $M B$. Поскольку множество
  $M B slash M B a$ конечно, существует лишь конечное число таких решеток. Итак,
  конечность числа $c_A (V)$ следует из конечности числа $c_B (V)$. В свою
  очередь конечность числа $c_B (V)$ непосредственно вытекает из следующего
  утверждения.
]

#proposition[
  Если $A$ — максимальный порядок, то существует лишь конечное число классов
  изоморфных неразложимых модулей $M in bold(italic(M)) (A)$ без кручения.
] <prop:maximal-order-indecomposable-lattices-finite>

#proof[
  В силу @th:hereditary-maximal-order-characterizations категория модулей
  $M in bold(italic(M)) (A)$ без кручения совпадает с $bold(italic(P)) (A)$. Эта
  категория естественно эквивалентна категории $bold(italic(P)) (B)$ для любой
  $R$-алгебры $B$, такой, что категории $italic("mod") "-" A$ и
  $italic("mod") "-" B$ эквивалентны. Из
  @th:hereditary-maximal-order-characterizations
  @cond:maximal-order-faithful-projective-generator и
  @cor:maximal-orders-division-algebra-endomorphisms следует, что можно найти
  такую алгебру $B$ вида $B=product B_i$, где каждый сомножитель $B_i$ является
  максимальным $R$-порядком в алгебре с делением над $L$. Так как
  $bold(italic(P)) (B)=product bold(italic(P)) (B_i)$, то, таким образом, мы
  свели нашу задачу к доказательству предложения для случая алгебры с делением
  $Lambda$. Опять из @th:hereditary-maximal-order-characterizations следует, что
  кольцо $A$ наследственно справа, а каждый модуль $P in bold(italic(P)) (A)$
  является прямой суммой модулей, изоморфных правым идеалам кольца $A$. Таким
  образом, каждый неразложимый модуль $P in bold(italic(P)) (A)$ изоморфен
  некоторому правому идеалу. Теперь наше утверждение вытекает из
  @prop:division-order-ideal-classes-finite.
]

#source(417)
#theorem[
  #condition-list[
    #condition-item(format: "cyrillic")[Абелевы группы $K_0(A)$ и $G_0(A)$
      конечно порождены.] <cond:arithmetic-k0-g0-finite-generation>
    #condition-item(format: "cyrillic")[Пусть кольцо $A$ удовлетворяет условию
      Картана. Тогда ядра всех гомоморфизмов диаграммы

      $ #diagram-cartan-class-number() $ <eq:arithmetic-cartan-class-number>

      конечны. Следовательно,

      $
        rank K_0(A)<=rank G_0(A)=rank G_0(Lambda)
        =("число простых факторов алгебры" Lambda).
      $]
    <cond:arithmetic-cartan-finite-kernels>
  ]
] <th:arithmetic-k0-g0-finite-generation>

#proof[
  Проведем его в несколько этапов.
  #condition-list[
    #condition-item(format: "degree")[_В случае
      @cond:arithmetic-cartan-finite-kernels $Ker (k_0)$ конечно, а
      следовательно, группа $K_0(A)$ конечно порождена._

      Элемент $x in Ker (k_0)$ можно записать в виде $x=[P]-[A^n]$; при этом
      $P tensor_R L tilde.eq Lambda^n$. Теперь из
      @cor:cartan-locally-free-splitting следует, что
      $P tilde.eq Q plus.o A^(n-1)$ для некоторого модуля $Q$. Таким образом,
      $x=[Q]-[A]$. Так как $Q$ является $A$-решеткой в
      $Q tensor_R L tilde.eq Lambda$, то существует лишь конечное число таких
      модулей $Q$ (см. @th:jordan-zassenhaus). Итак, $Ker (k_0)$ — конечное
      множество. Так как $K_0(Lambda)$ — свободная абелева группа конечного
      ранга, то группа $K_0(A)$ конечно порождена.]
    <cond:cartan-k0-kernel-finite>
    #condition-item(format: "degree")[_Группа $G_0(A)$ конечно порождена._

      Как мы видели, группа $G_0(A)$ порождается всеми элементами $[M]$, где
      модуль $M in bold(italic(M)) (A)$ без кручения. Таким образом, $M$ —
      $A$-решетка в $V=M tensor_R L$. Рассматривая ограничение на $M$ ряда
      Жордана — Гёльдера $Lambda$-модуля $V$, получим конечную фильтрацию модуля
      $M$, последовательные факторы которого являются $A$-решетками в простых
      $Lambda$-модулях. Таким образом, если $V_1,dots,V_m$ — различные простые
      $Lambda$-модули, то в обозначениях теоремы @th:jordan-zassenhaus группа
      $G_0(A)$ допускает систему образующих из $c_A (V_1)+dots+c_A (V_m)$
      элементов.]
    <cond:arithmetic-g0-lattice-generators>
    #condition-item(format: "degree")[_Ядра отображений $g_0$ и $c_0(A)$ в
      случае @cond:arithmetic-cartan-finite-kernels конечны._

      Из диаграммы @eq:arithmetic-cartan-localization-sequences §
      @sec:swan-triangle-cartan-condition извлечем коммутативную диаграмму

      $ #diagram-cartan-kernels() $

      с точными строками. В силу @prop:cartan-localization-torsion-cokernel
      коядра отображения $c_0(A,S)$, а следовательно, и отображения $h$ являются
      периодическими модулями. В силу @cond:cartan-k0-kernel-finite ядро
      $Ker (k_0)$ конечно. Следовательно, $Ker (g_0)$ — периодический модуль. Но
      из @cond:arithmetic-g0-lattice-generators следует, что группа
      #source(418)
      $Ker (g_0)$ конечно порождена. Следовательно, она конечна. Так как
      $Ker (c_0(A)) subset Ker (k_0)$, то из части @cond:cartan-k0-kernel-finite
      следует, что ядро $Ker (c_0(A))$ конечно.]
    <cond:arithmetic-cartan-g0-kernels-finite>
    #condition-item(format: "degree")[_Группа $K_0(A)$ конечно порождена._

      Можно вложить $A$ в максимальный порядок $B$ и выбрать $B$-идеал
      $frak(c) subset A$, как в @prop:order-conductor-mayer-vietoris. Тогда (в
      обозначениях из @prop:order-maximal-order-comparison) получаем точную
      последовательность

      $ K_1(B')->K_0(A)->K_0(A') plus.o K_0(B)->K_0(B'), $

      где $A'=A slash frak(c)$ и $B'=B slash frak(c)$ — конечные кольца. Кроме
      того, отображение $U(B')->K_1(B')$ сюръективно. Поэтому группа $K_1(B')$ —
      конечная группа, а $K_0(A')$ и $K_0(B')$ — свободные абелевы группы
      конечного ранга. Наконец, кольцо $B$ удовлетворяет условию Картана.
      Поэтому из части @cond:cartan-k0-kernel-finite следует, что группа
      $K_0(B)$ конечно порождена. Рассмотрение точной последовательности
      позволяет утверждать, что группа $K_0(A)$ конечно порождена, что и
      требовалось доказать.]
    <cond:arithmetic-k0-conductor-reduction>
  ]
  Это завершает доказательство теоремы @th:arithmetic-k0-g0-finite-generation.
]

#corollary[
  Пусть $B$ — конечномерная $R$-алгебра. Тогда $K_0(B)$ и $G_0(B)$ — конечно
  порожденные абелевы группы.
] <cor:finite-arithmetic-algebra-k0-g0>

#proof[
  В силу @prop:finite-algebra-semisimple-order-reduction существует наибольший
  двусторонний нильпотентный идеал $N subset B$, такой, что
  $B slash N tilde.eq T times A$, где $T$ — конечное полупростое кольцо, а $A$
  является $R$-порядком в полупростой алгебре (как и выше). В силу
  @prop:k-radical-ideal-comparison получим изоморфизмы
  $K_0(B) isoArrow K_0(B slash N)
  tilde.eq K_0(T) plus.o K_0(A)$. Аналогично из
  @prop:nilpotent-ideal-g-invariance получим изоморфизмы
  $G_0(T) plus.o G_0(A) tilde.eq G_0(B slash N) isoArrow G_0(B)$. Так как кольцо
  $T$ полупросто, то $K_0(T)=G_0(T)$ — свободная абелева группа конечного ранга.
  Из теоремы @th:arithmetic-k0-g0-finite-generation следует, что группы $K_0(A)$
  и $G_0(A)$ конечно порождены. Это завершает доказательство.
]

Наконец, рассмотрим группу Пикара.

#theorem[
  (Неабелева) группа $Pic_R (A)$ (см. гл. @ch:module-categories, §
  @sec:picard-group) конечна. Кроме того, имеет место точная последовательность

  $ 1 -> InAut (A) arrow^i Aut_(R hyph alg) (A) -> Pic_R (A). $

  Таким образом, коядро $Coker (i)$ (группа «внешних автоморфизмов» $R$-алгебры
  $A$) конечно.
] <th:arithmetic-picard-outer-automorphisms-finite>

#proof[
  Локализация $A->Lambda$ индуцирует гомоморфизм групп
  $Pic_R (A)->Pic_L (Lambda)$. Предложение @prop:semisimple-picard-finite
  утверждает, что группа $Pic_L (Lambda)$ конечна. Ядро состоит из элементов
  вида $[P]$, где $P$ — обратимый $A$-$A$-бимодуль (т. е. левый
  $A tensor_R A^o$-модуль), для которого бимодули $P tensor_R L$ и $Lambda$
  изоморфны.
  #source(419)
  Пусть $C$ — центр алгебры $Lambda$. Тогда $C$ — конечное произведение полей,
  содержащих поле $L$. Так как тензорное произведение центральных простых алгебр
  над полем опять является центральной простой алгеброй (см.
  @prop:semisimple-picard-finite), то легко показать, что
  $Lambda tensor_C Lambda^o$ — полупростая $L$-алгебра. Кроме того, образ $B$
  кольца $A tensor_R A^o$ в алгебре $Lambda tensor_C Lambda^o$ является
  $R$-порядком. Рассмотренный бимодуль $P$ оказывается $B$-решеткой в
  $Lambda tensor_C Lambda^o$-модуле $Lambda (tilde.eq P tensor_R L)$. Если $Q$ —
  другой такой бимодуль, то $A$-бимодули $P$ и $Q$ изоморфны тогда и только
  тогда, когда изоморфны левые $B$-модули $P$ и $Q$. Из теоремы Жордана —
  Цассенхауза @th:jordan-zassenhaus следует теперь, что существует лишь конечное
  число таких элементов $[P] in Ker (Pic_R (A)->Pic_L (Lambda))$. Следовательно,
  группа $Pic_R (A)$ конечна. Другие утверждения непосредственно вытекают из
  @prop:picard-twisted-bimodules. Теорема доказана.
]
