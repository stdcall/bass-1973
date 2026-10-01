#import "main-defs.typ": (
  Coker, Hom, Im, ann, codim, dim, fRank, idx, maxSpec, moduleCategory, rad,
  source, supp,
)
#import "statements.typ": (
  assertion, corollary, lemma, proof, proposition, theorem,
)

#source(145)
== Теорема Серра <sec:serres-theorem>

В следующих двух параграфах фиксированы:

#assertion(italic: false)[$R$ — коммутативное кольцо, такое, что
  $X = maxSpec(R)$ является нётеровым пространством, и $A$ — конечномерная
  $R$-алгебра.]
<ss:serre-ring-hypotheses>

Напомним, что для $M in moduleCategory hyph A$
$
  supp_frak(m) (M) = {frak(m) in X | M_frak(m) != 0}.
$
Если $M$ — конечно порожденный $A$-модуль, то
$
  supp_frak(m) (M) = V(ann_R (M))
  = {frak(m) in X | frak(m) supset ann_R (M)}
$
является замкнутым множеством (см. гл.~@ch:rings-modules,
§~@sec:chain-conditions-spectrum-dimension). Так как $A$ — конечномерная
$R$-алгебра, то кольцо $A_frak(m)$ полулокально для каждого $frak(m) in X$ и,
следовательно, можно определить для $P in moduleCategory hyph A$ и
$S subset P$
$
  fRank_A (S; P) = inf_(frak(m) in X) fRank_(A_frak(m)) (S; P_frak(m))
$
и
$
  fRank_A (P) = fRank_A (P; P).
$
Следующее утверждение является непосредственным следствием из
@cor:semilocal-free-rank-additivity и определения:

#proposition[
  Пусть $M$ — подмодуль модуля $P in moduleCategory hyph A$. Тогда
  $
    fRank_A (A^r plus.o M; A^r plus.o P) = r + fRank_A (M; P).
  $
] <prop:localized-free-rank-additivity>

Если теперь $P in moduleCategory hyph A$ и $S$ — подмножество в $P$, то
определим _сингулярные множества_#idx("сингулярное множество") для $S$ в $P$ при
любом $j >= 0$ формулой
$
  F_j (S; P) = {frak(m) in X | fRank_(A_frak(m)) (S; P_frak(m)) < j}.
$
Например, $F_0 (S; P) = emptyset$ для всех $S$ и $F_j (emptyset; P) = X$ для
всех $j > 0$.

#proposition[
  Пусть модуль $P in moduleCategory hyph A$ является прямым слагаемым прямой
  суммы конечно представимых модулей. Тогда для любого $S subset P$ и для любого
  $j >= 0$ множество $F_j (S; P)$ замкнуто в $X$.
] <prop:free-rank-singular-loci-closed>

#proof[
  Предположим, что $frak(m) in.not F_j (S; P)$. Тогда найдется расщепляющийся
  мономорфизм $h^1: A_frak(m)^j -> P_frak(m)$. Можно добиться, чтобы
  $h^1 = h_frak(m)$ для некоторого $h: A^j -> P$. Если мы покажем, что
  $U = {frak(n) | h_frak(n) "— расщепляющийся мономорфизм"}$ — открытое
  множество, то тогда $U$ и будет окрестностью точки $frak(m)$, не
  пересекающейся с $F_j (S; P)$, и это покажет, что $F_j (S; P)$ — замкнутое
  множество.

  #source(146)Пусть $P plus.o P' tilde.eq product.co_i Q_i$, где каждый модуль
  $Q_i$ конечно представим. Выберем конечную сумму $Q$ модулей $Q_i$ таким
  образом, чтобы $Im(h) subset Q$. Тогда [отображение $h: A^j -> P$ обладает
  левым обратным] $<=>$ [индуцированный гомоморфизм $A^j -> Q$ обладает левым
  обратным]. Следовательно, без потери общности можно считать, что модуль $P$
  конечно представим. В этом случае из
  @prop:localization-hom-finite-presentation следует, что естественное
  отображение $(P^*)_frak(n) -> (P_frak(n))^*$ является изоморфизмом для любого
  $frak(n) in X$. Это же, конечно, применимо и к $A^j$. Теперь, используя
  @prop:split-monomorphism-dual-radical
  @cond:split-monomorphism-dual-epimorphism, получаем
  $
    U & = {frak(n) in X | h_frak(n) "— расщепляющийся мономорфизм"} \
      & = {frak(n) in X | Coker((h_frak(n))^*) = 0} \
      & = {frak(n) in X | Coker((h^*)_frak(n)) = 0} \
      & = X without supp(Coker(h^*)).
  $
  Так как модуль $Coker(h^*: P^* -> (A^j)^*)$ конечно порожден, то его носитель
  замкнут, чем и завершается доказательство.
]

В последней части доказательства ясно, что $h$ расщепляется тогда и только
тогда, когда $h_frak(n)$ расщепляется для каждого $frak(n)$. Если
$alpha_1, dots, alpha_j$ — образ базиса модуля $A^j$, то мы приходим к
следующему заключению:

#corollary[
  Пусть $P$ то же, что и в предложении @prop:free-rank-singular-loci-closed, и
  $alpha_1, dots, alpha_j in P$. Элементы $alpha_1, dots, alpha_j$ образуют
  базис свободного прямого слагаемого модуля $P$ тогда и только тогда, когда
  $F_j (alpha_1, dots, alpha_j; P) = emptyset$. В частности, элемент
  $alpha in P$ унимодулярен в том и только том случае, когда
  $F_1 (alpha; P) = emptyset$.
] <cor:unimodular-local-global-criterion>

Перейдем теперь к основной теореме этого параграфа.

#theorem(title: [Серр])[
  #idx("теорема Серра")Пусть $V = V(frak(a))$ — замкнутое множество в $X$,
  такое, что $X without V$ есть объединение конечного числа непересекающихся
  подпространств, причем размерность каждого $<= d$. Пусть
  $P in moduleCategory hyph A$ является прямым слагаемым прямой суммы конечно
  представимых модулей и элемент $gamma in P$ таков, что $gamma$ — унимодулярный
  элемент в $P_frak(m)$ для всех $frak(m) in V$. Тогда если $fRank_A (P) > d$,
  то найдется унимодулярный элемент $alpha in P$, такой, что
  $alpha equiv gamma mod P frak(a)$.
] <th:serre-unimodular-element>

#corollary[
  Пусть $V$ и $P$ те же, что и выше. Допустим, что $fRank_A (P) >= d + r$ и что
  существуют элементы $gamma_1, dots, gamma_r in P$, порождающие прямое
  слагаемое в модуле $P_frak(m)$, изоморфное $A_frak(m)^r$, для всех
  $frak(m) in V$. (Например, это имеет место в том случае, когда модуль $P$
  проективен и модуль $P/(P frak(a))$ содержит прямое слагаемое, изоморфное
  $(A/(A frak(a)))^r$.) Тогда модуль $P$ содержит прямое слагаемое, изоморфное
  модулю $A^r$.
] <cor:serre-free-summand-with-congruences>

#source(147)
#proof[
  В силу теоремы Серра можно записать $P = alpha A plus.o P'$, где
  $alpha equiv gamma_1 mod P frak(a)$ и элемент $alpha$ унимодулярен.
  Утверждение устанавливается применением индукции к проекциям элементов
  $gamma_2, dots, gamma_r$ в $P'$.
]

#corollary[
  Пусть модуль $P$ такой же, как и ранее. Допустим, что $X$ — объединение
  конечного числа непересекающихся подпространств размерности $<= d$ (так будет,
  например, в случае $dim X <= d$). Тогда если $fRank_A (P) > d$, то $P$
  содержит унимодулярный элемент.
] <cor:serre-free-summand>

#proof[
  Возьмем $frak(a) = R$, тогда $V = emptyset$.
]

*Замечание.* Из предположений следствия @cor:serre-free-summand не вытекает, что
$dim X <= d$. Например, пусть $R$ — полулокальное нётерово кольцо размерности
$d > 0$, и пусть $A = R[t]$, где $t$ — переменная. Тогда
$dim maxSpec(A) = d + 1$, в то время как $maxSpec(A)$ является объединением
замкнутого множества и открытого множества, при этом размерность каждого из них
$<= d$ (см. @prop:group-ring-maximal-dimension-bound).

Доказательство теоремы @th:serre-unimodular-element будет основано на двух
леммах. Пусть $Y_1, dots, Y_N$ — непересекающиеся подпространства в
$X without V$. Напомним (см. @prop:noetherian-topological-components), что все
подпространства в $X$ нётеровы. Кроме того, в силу наших предположений о модуле
$P$ из @prop:free-rank-singular-loci-closed следует, что $F_j (S; P)$ —
замкнутое подмножество в $X$ для всех $S subset P$ и всех $j >= 0$. Приведем
теперь леммы.

#lemma[
  Предположим, что $fRank_A (P) >= r$. Тогда для заданных элементов
  $gamma_1, dots, gamma_r in P$ найдутся такие элементы
  $alpha_1, dots, alpha_r in P$, что $alpha_i equiv gamma_i mod P frak(a)$
  ($1 <= i <= r$) и
  $codim_(Y_i) (Y_i inter F_j (alpha_1, dots, alpha_r; P)) >= r + 1 - j$
  ($j >= 0$; $1 <= i <= N$).
] <lem:serre-singular-locus-codimension>

#lemma[
  Предположим, что $alpha_1, dots, alpha_r in P$ ($r >= 1$) и $k >= 0$, причем
  $
    codim_(Y_i) (Y_i inter F_j (alpha_1, dots, alpha_r; P)) >= k - j
    quad (1 <= j <= r, quad 1 <= i <= N).
  $
  Тогда найдутся элементы $beta_i = alpha_i + alpha_r a_i$ ($a_i in A$,
  $1 <= i < r$), такие, что
  $
    codim_(Y_i) (Y_i inter F_j (beta_1, dots, beta_(r-1); P)) >= k - j
    quad (1 <= j <= r - 1, quad 1 <= i <= N).
  $
] <lem:serre-codimension-generator-reduction>

#proof(head: [Доказательство того, что из лемм
  @lem:serre-singular-locus-codimension и
  @lem:serre-codimension-generator-reduction следует теорема
  @th:serre-unimodular-element.])[
  По предположению можно выбрать $Y_i$ так, чтобы
  $X = V union Y_1 union dots union Y_N$. Кроме того, можно применить
  @lem:serre-singular-locus-codimension при $r = d + 1$. При этом мы возьмем
  $gamma_1 = gamma$ (из @th:serre-unimodular-element) и $gamma_i = 0$ для
  $i > 1$. Тогда из @lem:serre-singular-locus-codimension следует, что #source(
    148,
  )найдутся элементы $alpha_1, dots, alpha_r in P$, такие, что
  $
    alpha_1 equiv gamma mod P frak(a), quad
    alpha_i equiv 0 mod P frak(a) quad (2 <= i <= r)
  $ <eq:serre-preserved-congruences>
  и
  $
    codim_(Y_i) (Y_i inter F_j (alpha_1, dots, alpha_r; P)) >= r + 1 - j
    quad (j >= 0, quad 1 <= i <= N).
  $
  В этой ситуации применим @lem:serre-codimension-generator-reduction
  последовательно $r - 1$ раз. В результате получим один элемент $alpha$, такой,
  что
  $
    codim_(Y_i) (Y_i inter F_1 (alpha; P)) >= r + 1 - 1 = r = d + 1
  $
  ($1 <= i <= N$). Так как $dim Y_i <= d$ (наше предположение), то отсюда
  следует, что $F_1 (alpha; P) inter Y_i = emptyset$ ($1 <= i <= N$). Кроме
  того, преобразование $alpha_i arrow.r.bar beta_i = alpha_i + alpha_r a_i$,
  использованное в @lem:serre-codimension-generator-reduction, сохраняет
  сравнения в @eq:serre-preserved-congruences, т.~е.
  $beta_1 equiv gamma mod P frak(a)$ и $beta_i equiv 0 mod P frak(a)$
  ($1 < i < r$). Таким образом, $alpha equiv gamma mod P frak(a)$. Так как в
  силу предположения $gamma$ — унимодулярный элемент по модулю $P frak(a)$, то
  таким же является и $alpha$, и, следовательно,
  $F_1 (gamma; P) inter V(frak(a)) = emptyset$. Так как $X$ — объединение $V$ и
  $Y_i$, то это показывает, что $F_1 (alpha; P) = emptyset$. Следовательно, в
  виду @cor:unimodular-local-global-criterion элемент $alpha$ унимодулярен, что
  и требовалось доказать.
]

#proof(head: [Доказательство леммы @lem:serre-singular-locus-codimension.])[
  Проведем индукцию по $r$. Случай $r = 0$ тривиален. Предположим, что $r >= 0$
  и $fRank_A (P) >= r + 1$. Если нам даны элементы
  $gamma_1, dots, gamma_(r+1) in P$, то можно, как и в
  @lem:serre-singular-locus-codimension, построить по индукции элементы
  $alpha_1, dots, alpha_r in P$. Подберем теперь элемент $alpha_(r+1)$.
  Напомним, что
  $
    alpha_i equiv gamma_i mod P frak(a) quad (1 <= i <= r)
  $
  и
  $
    codim_(Y_i) (Y_i inter F_j) >= r + 1 - j
    quad (j >= 0; quad 1 <= i <= N),
  $
  где $F_j = F_j (alpha_1, dots, alpha_r; P)$. Зафиксируем $j$, $0 <= j <= r$, и
  пусть $C$ — неприводимая компонента пространства $Y_i inter F_(j+1)$, такая,
  что
  $
    codim_(Y_i) (C) = (r + 1) - (j + 1) = r - j.
  $
  Так как
  $
    codim_(Y_i) (Y_i inter F_j) >= r + 1 - j > r - j,
  $
  то $C subset.not F_j$. Варьируя $C$, видим, что существуют _конечные_
  множества $D_j$ ($0 <= j <= r$), такие, что
  $
    D_j subset F_(j+1), quad D_j inter F_j = emptyset, quad
    D_j inter V = emptyset,
  $
  причем для каждого $i$ множество $D_j$ содержит точку в каждой из компонент
  пространства $Y_i inter F_(j+1)$ коразмерности $r - j$ в $Y_i$
  ($1 <= i <= N$).

  #source(149)Если $frak(m) in D_j$, то $fRank$ элементов
  $alpha_1, dots, alpha_r$ в $P_frak(m)$ не меньше $j$. Следовательно, так как
  $fRank(P) >= r + 1 > r >= j$, то найдется элемент
  $alpha(frak(m)) in P_frak(m)$ (который можно даже выбрать из $P$), такой, что
  $fRank$ элементов $alpha_1, dots, alpha_r, alpha(frak(m))$ в $P_frak(m)$ не
  меньше $j + 1$. Это легко следует из @cor:semilocal-free-rank-additivity.

  Пусть $D = union D_j$ ($0 <= j <= r$). В силу китайской теоремы об остатках
  @prop:chinese-remainder-modules мы можем найти элемент $alpha_(r+1) in P$, для
  которого $alpha_(r+1) equiv gamma_(r+1) mod P frak(a)$ и
  $alpha_(r+1) equiv alpha(frak(m)) mod P frak(m)$ для каждого $frak(m) in D$.
  Тогда если $frak(m) in D_j$, то из @prop:free-rank-radical-invariance следует,
  что $frak(m) in.not F'_(j+1) = F_(j+1) (alpha_1, dots, alpha_(r+1); P)$. Здесь
  использовано то, что $A_frak(m) dot frak(m) subset rad A_frak(m)$. Очевидно,
  что $F'_(j+1) subset F_(j+1)$. Кроме того, мы знаем, что
  $
    codim_(Y_i) (Y_i inter F_(j+1)) >= (r + 1) - (j + 1) = r - j.
  $
  Так как $F'_(j+1)$ не содержит по крайней мере одну точку из каждой компоненты
  коразмерности $r - j$ в $Y_i inter F_(j+1)$, то
  $
    codim_(Y_i) (Y_i inter F'_(j+1)) >= r - j + 1
    = (r + 1) + 1 - (j + 1)
  $
  ($0 <= j <= r$). Поскольку $F'_0 = emptyset$ и $(r + 1) + 1 - (j + 1) <= 0$
  для $j > r$, приведенное неравенство справедливо при всех $j >= 0$
  ($1 <= i <= N$). Лемма доказана.
]

#proof(head: [Доказательство леммы
  @lem:serre-codimension-generator-reduction.])[
  Нам даны элементы $alpha_1, dots, alpha_r in P$, такие, что
  $
    codim_(Y_i) (Y_i inter F_j) >= k - j
    quad (1 <= i <= N; quad 0 <= j <= r),
  $
  где $F_j = F_j (alpha_1, dots, alpha_r; P)$. Предположим, что $0 <= j < r$.
  Тогда для каждого $i$ компонента пространства $Y_i inter F_(j+1)$
  коразмерности $k - (j + 1)$ не может содержаться в $F_j$. Следовательно, можно
  выбрать конечное множество $D_j subset F_(j+1)$, такое, что
  $D_j inter F_j = emptyset$ и $D_j$ содержит для любого $i$ одну точку из
  каждой неприводимой компоненты пространства $Y_i inter F_(j+1)$ коразмерности
  $k - (j + 1)$. Поэтому если $frak(m) in D_j$, то $fRank$ элементов
  $alpha_1, dots, alpha_r$ в $P_frak(m)$ равен $j < r$. Следовательно, можно
  применить @prop:semilocal-free-rank-generator-reduction, в силу чего найдутся
  элементы
  $
    beta_i (frak(m)) = alpha_i + alpha_r a_i (frak(m))
    quad (a_i (frak(m)) in A_frak(m), quad 1 <= i < r),
  $
  такие, что $fRank_(A_frak(m)) (beta_1 (frak(m)), dots,
    beta_(r-1) (frak(m)); P_frak(m)) >= j$. Так как идеал $frak(m)$
  максимальный, то $A_frak(m)/(frak(m) dot A_frak(m)) = A/(frak(m) dot A)$.
  Следовательно, по китайской теореме об остатках можно найти элементы
  $a_i in A$, такие, что $a_i equiv a_i (frak(m)) mod frak(m) dot A_frak(m)$ для
  каждого $frak(m) in union_j D_j$ ($0 <= j < r$). Положим теперь
  $beta_i = alpha_i + alpha_r a_i$ ($1 <= i < r$). Тогда подмодули
  $(alpha_1, dots, alpha_(r-1), alpha_r)$ и
  $(beta_1, dots, beta_(r-1), alpha_r)$ модуля $P$ совпадают, и поэтому из
  @cor:free-rank-one-generator-bound следует, что
  $
    F'_j & = F_j (beta_1, dots, beta_(r-1); P) \
         & subset F_(j+1) (beta_1, dots, beta_(r-1), alpha_r; P) = F_(j+1).
  $
  #source(150)С другой стороны, если $frak(m) in D_j$, то
  $beta_i equiv beta_i (frak(m)) mod P_frak(m) dot frak(m)$ (с учетом сравнений
  для элементов $a_i$), и потому из @prop:free-rank-radical-invariance вытекает,
  что
  $
    fRank_(A_frak(m)) (beta_1, dots, beta_(r-1); P_frak(m))
    = fRank(beta_1 (frak(m)), dots, beta_(r-1) (frak(m)); P_frak(m)) >= j.
  $
  Таким образом, $F'_j inter D_j = emptyset$ и, значит, $F'_j$ не содержит для
  каждого $i$ по одной точке из каждой компоненты пространства
  $Y_i inter F_(j+1)$ коразмерности $k - (j + 1)$ в $Y_i$. Отсюда следует, что
  $codim_(Y_i) (Y_i inter F'_j) >= k - j$, чем и завершается доказательство.
]
