#import "main-defs.typ": (
  Aut, E, GE, GL, Int, Ker, SL, U, det, diag, directLim, idx, source,
  symbol-idx, transpose,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, numbered-condition, proof,
  proposition,
)

#heading(level: 2)[Элементарные матрицы и конгруэнцподгруппы]
<sec:elementary-matrices-congruence-subgroups>

Пусть $A$~— кольцо. Тогда $GL_n (A) = Aut_A (A^n)$, где
$A^n = A plus.o dots plus.o A$~— стандартный свободный правый $A$-модуль.
Полагаем
$
  E_n (A) = E(A, dots, A),
$
где обозначение совпадает с принятым в
(§~@sec:cancellation-elementary-automorphisms
гл.~@ch:stable-projective-structure). Если мы отождествим (что будем часто
делать) эндоморфизмы модуля $A^n$ с соответствующими матрицами, то группа
$E_n (A)$ порождается _элементарными матрицами_#idx("элементарная матрица")
$epsilon = I_n + a e_(i j)$ ($a in A$, $i != j$), где $e_(i j)$ обозначает
матрицу, у которой на месте $(i, j)$ стоит $1$, а на всех остальных местах нули.
Матрицу $epsilon$ будем называть _$frak(q)$-элементарной_#idx(
  "q-элементарная матрица",
) (где $frak(q)$~— двусторонний идеал кольца $A$), если $a in frak(q)$. Группа
$
  E_n (A, frak(q)) = E(A, dots, A; frak(q))
$
(опять в обозначениях из (§~@sec:cancellation-elementary-automorphisms
гл.~@ch:stable-projective-structure)) является, таким образом, _нормальным
делителем_ группы $E_n (A)$, порожденным всеми $frak(q)$-элементарными
матрицами. Как частный случай утверждения
@prop:elementary-group-quotient-surjection получаем

#proposition[
  Пусть $frak(q)$~— двусторонний идеал кольца $A$ и $f: A -> B$~— сюръективный
  гомоморфизм колец. Тогда $f$ индуцирует эпиморфизм
  $E_n (A, frak(q)) -> E_n (B, f(frak(q)))$ для всех $n >= 1$.
] <prop:elementary-matrices-quotient-surjection>

#proposition[
  Пусть $A$~— кольцо, $a, b in A$ и $u, v in U(A)$. Тогда справедливы следующие
  утверждения о группе $GL_n (A)$:
  #condition-list[
    #condition-item(format: "cyrillic")[если $i != j$, то отображение
      $A -> GL_n (A)$, при котором $a arrow.r.bar I + a e_(i j)$, является
      мономорфизмом групп;] <cond:elementary-additive-embedding>

    #condition-item(format: "cyrillic")[если числа $i$, $j$ и $k$ различны (и
      поэтому $n >= 3$), то $[I + a e_(i j), I + b e_(j k)] = I + a b e_(i k)$;]
    <cond:elementary-matrix-commutator>

    #condition-item(format: "cyrillic")[
      $
        mat(1, a; 0, 1)^mat(u, b; 0, v)
        = mat(1, u^(-1) a v; 0, 1)
      $
      и
      $
        [mat(1, a; 0, 1), mat(u, b; 0, v)]
        = mat(1, u^(-1) a v - a; 0, 1).
      $
    ] <cond:elementary-upper-triangular-conjugation>
  ]
] <prop:elementary-matrix-identities>

#proof[
  #source(183)Напомним, что $e_(i j) e_(k h) = delta_(j k) e_(i h)$.
  Следовательно, если $i != j$, то $e_(i j)^2 = 0$, и отсюда вытекает
  @cond:elementary-additive-embedding.
  @cond:elementary-matrix-commutator
  $
    [I + a e_(i j), I + b e_(j k)]
    = (I - a e_(i j) - b e_(j k) + a b e_(i k)) dot
    (I + a e_(i j) + b e_(j k) + a b e_(i k))
    = (I - a e_(i j) - b e_(j k) + a b e_(i k))
    + (a e_(i j)) + (b e_(j k) - a b e_(i k)) + (a b e_(i k))
    = I + a b e_(i k).
  $
  @cond:elementary-upper-triangular-conjugation
  $
    mat(u, b; 0, v) = mat(1, b v^(-1); 0, 1) mat(u, 0; 0, v),
  $
  при этом первый множитель перестановочен с матрицей $I + a e_(1 2)$.
  Следовательно,
  $
    mat(1, a; 0, 1)^mat(u, b; 0, v)
    = mat(u^(-1), 0; 0, v^(-1)) mat(1, a; 0, 1) mat(u, 0; 0, v)
    = mat(1, u^(-1) a v; 0, 1)
  $
  и
  $
    [mat(1, a; 0, 1), mat(u, b; 0, v)]
    = mat(1, -a; 0, 1) mat(1, u^(-1) a v; 0, 1)
    = mat(1, u^(-1) a v - a; 0, 1),
  $
  что и требовалось доказать.
]

#corollary[
  Если $A$~— конечно порожденная $Int$-алгебра, то $E_n (A)$~— конечно
  порожденная группа для всех $n >= 3$. Если $A$~— конечномерная $Int$-алгебра,
  то группа $E_2 (A)$ также конечно порождена.
] <cor:elementary-group-finite-generation>

#proof[
  Группа $E_n (A)$ порождается конечным числом подгрупп, каждая из которых
  изоморфна аддитивной группе кольца $A$ (в силу
  @prop:elementary-matrix-identities @cond:elementary-additive-embedding), а это
  доказывает последнее утверждение.

  Предположим, что элементы $a_0 = 1$, $a_1, dots, a_r$ порождают $A$ как
  кольцо. Пусть $S = {I + a_i e_(j k) | 0 <= i <= r, 1 <= j, k <= n, j != k}$
  (это конечное множество). Так как $n >= 3$, то по индукции из утверждения
  @prop:elementary-matrix-identities @cond:elementary-matrix-commutator следует,
  что группа, порожденная множеством $S$, содержит все матрицы $I + M e_(i j)$
  для всех $i != j$ и всех одночленов $M$ от элементов $a_0, dots, a_r$. Так как
  эти одночлены $M$ порождают аддитивно кольцо $A$, то из
  @prop:elementary-matrix-identities @cond:elementary-additive-embedding теперь
  вытекает, что множество $S$ порождает группу $E_n (A)$, что и требовалось
  доказать.
]

#corollary[
  Допустим, что $n >= 3$. Пусть $H subset GL_n (A)$~— подгруппа, нормализуемая
  группой $E_n (A)$. Пусть $T$~— совокупность элементарных матриц, содержащихся
  в $H$. Тогда $H supset E_n (A, frak(q))$, где $frak(q)$~— двусторонний идеал,
  порожденный координатами матриц $I - sigma$, где $sigma$ пробегает множество
  $T$.
] <cor:elementary-level-containment>

#proof[
  #source(184)Если $sigma = I + a e_(i j) in T$, то из
  @prop:elementary-matrix-identities @cond:elementary-matrix-commutator следует
  (поскольку $n >= 3$), что $H$ содержит все матрицы вида $I + b a c e_(h k)$
  ($b, c in A$; $h != k$). Заметим, что $E_n (A)$-нормализуемая подгруппа,
  порожденная этими матрицами, совпадает с $E_n (A, A a A)$. Варьируя теперь
  $sigma$, легко получить утверждение следствия, что и требовалось.
]

#corollary[
  Допустим, что $n >= 3$. Пусть $frak(q)$ и $frak(q)'$~— двусторонние идеалы
  кольца $A$. Тогда
  $
    E_n (A, frak(q) frak(q)')
    subset [E_n (A, frak(q)), E_n (A, frak(q)')].
  $
  В частности,
  $
    E_n (A, frak(q)) = [E_n (A), E_n (A, frak(q))].
  $
] <cor:relative-elementary-commutators>

#proof[
  Группа $[E_n (A, frak(q)), E_n (A, frak(q)')]$ нормализуется подгруппой
  $E_n (A)$. Из утверждения @prop:elementary-matrix-identities
  @cond:elementary-matrix-commutator следует, что она содержит все
  $frak(q) frak(q)'$-элементарные матрицы. Применим теперь
  @cor:elementary-level-containment. Так как группа $E_n (A)$ нормализует
  $E_n (A, frak(q))$, то $E_n (A, frak(q)) supset [E_n (A), E_n (A, frak(q))]$.
]

Введем некоторые обозначения, которые будут использоваться как в этой, так и в
следующих главах. Пусть $A$~— кольцо. Для $n, m >= 1$ будем рассматривать группу
$GL_n (A)$ как подгруппу группы $GL_(n + m) (A)$ с помощью мономорфизма
$
  alpha arrow.r.bar alpha plus.o I_m = mat(alpha, 0; 0, I_m)
  quad (GL_n (A) subset GL_(n + m) (A)).
$
Переходя к пределу, получаем
$
  GL(A) = union.big_n GL_n (A) (= #directLim($n$) GL_n (A)).
$
Можно представлять себе элементы группы $GL(A)$ как бесконечные матрицы
$
  mat(alpha, , , , 0; , 1; , , 1; , , , dots.down; 0, , , , dots.down)
  quad (alpha in GL_n (A) "для некоторого" n).
$
В частности, мы отождествляем таким образом группу $U(A) = GL_1 (A)$ с
множеством диагональных матриц $diag(u, 1, dots, 1)$ группы $GL_n (A)$ при любом
$n$. Диагональные матрицы образуют подгруппу
$
  D_n (A) = {"диагональные матрицы в" GL_n (A)}.
$

#source(185)Пусть $frak(q)$~— двусторонний идеал кольца $A$. Определим _главную
конгруэнцподгруппу уровня $frak(q)$_#idx(
  "главная конгруэнцподгруппа уровня q",
) в группе $GL_n (A)$:
$
  GL_n (A, frak(q)) = Ker(GL_n (A) -> GL_n (A slash frak(q))).
$#symbol-idx(
  $GL_n (A, frak(q))$,
  sort: "GL_n(A,q)",
  group: "groups",
  order: 102,
)
Более общим образом будем говорить, что $H subset GL_n (A)$ является _подгруппой
уровня $frak(q)$_,#idx("подгруппа уровня q") если $H$~— подгруппа и
$
  E_n (A, frak(q)) subset H subset GL_n (A, frak(q)).
$
#numbered-condition[
  _Если $n >= 2$, то уровень подгруппы $H$ определен однозначно._
] <eq:congruence-subgroup-unique-level>
Чтобы убедиться в этом, покажем, что если
$E_n (A, frak(q)) subset GL_n (A, frak(q)')$, то $frak(q) subset frak(q)'$.
Пусть $f: A -> A slash frak(q)'$. Тогда из нашего предположения и из предложения
@prop:elementary-matrices-quotient-surjection следует, что
$E_n (A slash frak(q)', f(frak(q))) = {1}$. Так как $n >= 2$, то отсюда
вытекает, что $f(frak(q)) = {0}$, т.~е. что $frak(q) subset frak(q)'$.

Если $alpha$ есть $(m times n)$-матрица над кольцом $A$, то через
$
  #transpose($alpha$, mark: $T$)
$#symbol-idx(
  $#transpose($alpha$, mark: $T$)$,
  sort: "superscript T",
  group: "superscripts",
  order: 152,
)
обозначим _транспонированную_ матрицу к матрице $alpha$, которая является
$(n times m)$-матрицей над кольцом $A^o$ (а не над $A$!). Если произведение
$alpha beta$ определено, то определено произведение $#transpose(
  $beta$,
  mark: $T$,
) #transpose($alpha$, mark: $T$)$, и оно совпадает с $#transpose(
  $(alpha beta)$,
  mark: $T$,
)$. В частности, мы получили антиизоморфизм колец
$
  M_n (A) arrow.r^T M_n (A^o).
$
Заметим, что $M_n (A) = M_n (A^o)$ как множества и, следовательно, имеет смысл
(и это справедливо) говорить, что все введенные группы инвариантны относительно
транспонирования.

Если кольцо $A$ коммутативно, то мы знаем, что такое определитель матрицы, и
можем рассмотреть
$
  SL_n (A) = Ker(GL_n (A) arrow.r^det U(A)).
$
Положим
$
  SL_n (A, frak(q)) = SL_n (A) inter GL_n (A, frak(q)),
  quad SL(A, frak(q)) = union.big_n SL_n (A, frak(q)).
$#symbol-idx(
  $SL_n (A, frak(q))$,
  sort: "SL_n(A,p)",
  group: "groups",
  order: 121,
)
#symbol-idx($SL(A, frak(q))$, sort: "SL(A,q)", group: "groups", order: 120)
Вложение $U(A) = GL_1 (A) subset GL_n (A)$ является правым обратным для
отображения $det$. Таким образом,
$
  E_n (A, frak(q)) subset SL_n (A, frak(q)) subset GL_n (A, frak(q))
  = U(A, frak(q)) SL_n (A, frak(q)).
$
Как и раньше, все эти подгруппы инвариантны относительно транспонирования.

Определим, далее,
$
  D_n (A, frak(q)) = D_n (A) inter GL_n (A, frak(q)).
$#symbol-idx($D_n (A, frak(q))$, sort: "D_n(A,q)", group: "letters", order: 85)

#source(186)В случае когда $n = 1$,
$U(A, frak(q)) = GL_1 (A, frak(q)) = D_1 (A, frak(q))$. Группу, порожденную
подгруппами $E_n (A, frak(q))$ и $D_n (A, frak(q))$, обозначим через
$
  GE_n (A, frak(q)).
$#symbol-idx($GE_n (A, frak(q))$, sort: "GE_n(A,q)", group: "groups", order: 98)
Введенные подгруппы «стабильны» в том смысле, что вложения
$GL_n (A) subset GL_(n + m) (A)$ индуцируют вложения соответствующих подгрупп.
Таким образом, можно ввести:
$
  E(A) = union.big_n E_n (A),
$
$
  E(A, frak(q)) = union.big_n E_n (A, frak(q)),
$
$
  GL(A, frak(q)) = union.big_n GL_n (A, frak(q)),
$
$
  D(A, frak(q)) = union.big_n D_n (A, frak(q)),
$
$
  GE(A, frak(q)) = union.big_n GE_n (A, frak(q))
$#symbol-idx($E(A)$, sort: "E(A)", group: "groups", order: 86)
#symbol-idx($E(A, frak(q))$, sort: "E(A,q)", group: "groups", order: 88)
#symbol-idx($GL(A, frak(q))$, sort: "GL(A,q)", group: "groups", order: 101)
#symbol-idx($D(A, frak(q))$, sort: "D(A,q)", group: "letters", order: 84)
#symbol-idx($GE(A, frak(q))$, sort: "GE(A,q)", group: "groups", order: 97)
и т.~д.

#proposition[
  $E_n (Int) = SL_n (Int)$ и $GE_n (Int) = GL_n (Int)$ для любого $n > 1$.
] <prop:integral-elementary-linear-groups>

#proof[
  Так как кольцо $Int$ евклидово, то утверждение следует из
  @prop:euclidean-ring-generalized-euclidean.
]

Следующий результат является основным во всем дальнейшем. Из него следует, что
по модулю подгрупп элементарных матриц групповой закон в $GL$ и взятие прямой
суммы совпадают.

#proposition(title: [«лемма Уайтхеда»])[
  Предположим, что $a in GL_n (A)$ и $b in GL_n (A, frak(q))$, где $frak(q)$~—
  двусторонний идеал кольца $A$. Тогда
  $
    mat(a, 0; 0, b) equiv mat(a b, 0; 0, I) equiv mat(b a, 0; 0, I)
    mod E_(2 n) (A, frak(q))
    equiv mat(0, a; -b, 0) mod E_(2 n) (A).
  $
  Эти сравнения применимы как к левым, так и к правым смежным классам.
] <prop:whitehead-lemma>
#idx("лемма Уайтхеда")

#proof[
  Приведем доказательство для левых смежных классов. Доказательство для правых
  смежных классов аналогично (это также можно вывести из первого утверждения,
  заметив, что все входящие подгруппы инвариантны относительно
  транспонирования).

  #source(187)Заметим сначала, что
  $
    mat(0, a; -b, 0) = mat(a, 0; 0, b) mat(0, I; -I, 0).
  $
  Из предложения @prop:integral-elementary-linear-groups следует, что
  $mat(0, I; -I, 0) in E_(2 n) (A)$. Запишем $b = I + q$, так что все элементы
  матрицы $q$ лежат в $frak(q)$. Непосредственная выкладка показывает, что
  $
    mat(b, 0; 0, b^(-1)) = mat(I, q; 0, I) mat(I, 0; I, I)
    mat(I, -b^(-1) q; 0, I)
    mat(I, 0; -b, I)
    = mat(I, q; 0, I)
    mat(I, -b^(-1) q; 0, I)^mat(I, 0; -I, I)
    mat(I, 0; -q, I) in E_(2 n) (A, frak(q)).
  $
  Таким образом,
  $
    mat(a b, 0; 0, I) = mat(a, 0; 0, b) mat(b, 0; 0, b^(-1))
    equiv mat(a, 0; 0, b) mod E_(2 n) (A, frak(q)).
  $
  Наконец,
  $
    mat(b a, 0; 0, I)^(-1) mat(a, 0; 0, b)
    = mat(a^(-1) b^(-1) a, 0; 0, b)
    = mat(I, (b a)^(-1) q; 0, I)
    mat(I, -a^(-1) q; 0, I)^mat(I, 0; a, I)
    mat(I, 0; -b^(-1) q a, I) in E_(2 n) (A, frak(q)).
  $
  Предложение доказано.
]

#corollary[
  Пусть $frak(q)$~— двусторонний идеал кольца $A$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[если
      $alpha_1, dots, alpha_m in GL_n (A, frak(q))$, то
      $
        diag(alpha_1, dots, alpha_m)
        equiv diag(alpha_1 dots alpha_m, I, dots, I)
        mod E_(n m) (A, frak(q));
      $
    ] <cond:relative-block-diagonal-product>

    #condition-item(format: "cyrillic")[группа $D_n (A)$ нормализует
      $E_n (A, frak(q))$, и
      $GE_n (A, frak(q)) = U(A, frak(q)) dot E_n (A, frak(q))$;]
    <cond:relative-general-elementary-factorization>

    #condition-item(format: "cyrillic")[группа $GE_n (A)$ содержит все
      обобщенные матрицы перестановок (определение дано в доказательстве).]
    <cond:generalized-permutation-elementary-containment>
  ]
] <cor:block-diagonal-elementary-congruences>

#proof[
  @cond:relative-block-diagonal-product В силу леммы Уайтхеда
  $
    diag(alpha_1, dots, alpha_m) equiv diag(alpha_1, dots, alpha_m)
    diag(I, dots, I, alpha_m, alpha_m^(-1))
    = diag(alpha_1, dots, alpha_(m - 1) alpha_m, I)
    mod E_(n m) (A, frak(q)).
  $
  Теперь @cond:relative-block-diagonal-product доказывается индукцией по $m$.

  @cond:relative-general-elementary-factorization Если $delta in D_n (A)$ и если
  матрица $epsilon$ является $frak(q)$-элементарной, то из утверждения
  @prop:elementary-matrix-identities
  @cond:elementary-upper-triangular-conjugation следует, что матрица
  $epsilon^delta$ также $frak(q)$-элементарна. В том случае, когда
  $frak(q) = A$, это показывает, что #source(188)матрица $delta$ нормализует
  $E_n (A)$. В общем случае подгруппа $E_n (A, frak(q))$ порождается элементами
  вида $epsilon^sigma$, где $epsilon$~— матрица рассмотренного типа и
  $sigma in E_n (A)$. Как мы убедились, $epsilon^delta$ является
  $frak(q)$-элементарной матрицей и $sigma^delta in E_n (A)$, поэтому
  $(epsilon^sigma)^delta = (epsilon^delta)^(sigma^delta) in
  E_n (A, frak(q))$. Таким образом, $D_n (A)$, а следовательно, и
  $U(A) subset D_n (A)$ нормализуют $E_n (A, frak(q))$. Из части
  @cond:relative-block-diagonal-product следует, что группа, порожденная
  группами $U(A, frak(q))$ и $E_n (A, frak(q))$, содержит $D_n (A, frak(q))$,
  что доказывает утверждение @cond:relative-general-elementary-factorization.

  @cond:generalized-permutation-elementary-containment Обобщенной матрицей
  перестановки#idx("обобщенная матрица перестановки") называется матрица вида
  $delta pi$, где $delta in D_n (A)$ и где $pi$~— матрица перестановки \[т.~е.
  обратимая матрица с единственным ненулевым (и равным $1$) элементом в каждой
  строке\]. Из предложения @prop:integral-elementary-linear-groups следует, что
  $pi = diag(plus.minus 1, 1, dots, 1) dot epsilon$, где $epsilon in E_n (A)$.
  Следовательно, $delta pi in GE_n (A)$.
]

#corollary[
  Пусть $frak(q)$~— двусторонний идеал кольца $A$. Тогда
  $[GL_n (A), GL_n (A, frak(q))] subset E_(2 n) (A, frak(q))$.
] <cor:linear-commutator-doubled-rank>

#proof[
  Пусть $a in GL_n (A)$ и $b in GL_n (A, frak(q))$. Тогда в силу леммы Уайтхеда
  в группе $GL_(2 n) (A)$ справедливо равенство
  $
    [mat(a, 0; 0, I), mat(b, 0; 0, I)]
    = mat(a^(-1) b^(-1), 0; 0, I) mat(a b, 0; 0, I)
    = epsilon_1 mat(a^(-1), 0; 0, b^(-1))
    mat(a, 0; 0, b) epsilon_2
    = epsilon_1 epsilon_2 in E_(2 n) (A, frak(q))
  $
  для подходящих матриц $epsilon_1, epsilon_2 in E_(2 n) (A, frak(q))$.
]
