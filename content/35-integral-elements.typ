#import "main-defs.typ": (
  End, ann, deg, det, dim, idx, maxSpec, moduleCategory, nil, rad, source, spec,
  supp, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, lemma, proof, proposition,
)

== Целые величины
<sec:integral-elements>

Пусть $R$ — коммутативное кольцо, $A$ — произвольная $R$-алгебра. Если $X in A$,
то через $R[X]$ обозначим $R$-подалгебру в $A$, порожденную элементом $X$.
Назовем элемент $a in A$ _целым_ над $R$, если он удовлетворяет условиям
сформулированного ниже предложения @prop:integral-element-characterizations.
Алгебра $A$ называется _целой_ над $R$, если каждый ее элемент целый. #idx(
  "целый элемент",
)#idx("целый элемент алгебры")#idx("целая алгебра")

#proposition[
  Следующие условия эквивалентны:
  #condition-list[
    #condition-item[$f(a) = 0$ для некоторого многочлена $f(T) in R[T]$ со
      старшим коэффициентом, равным $1$;] <cond:integral-monic-equation>

    #condition-item[#source(103) $R$-модуль $R[a]$ конечно
      порожден;] <cond:integral-finite-subalgebra>

    #condition-item[существует точный $R[a]$-модуль $M$, который как $R$-модуль
      конечно порожден.] <cond:integral-faithful-finite-module>
  ]
] <prop:integral-element-characterizations>
#proof[
  $#[@cond:integral-monic-equation] => #[@cond:integral-finite-subalgebra]$.
  Если $r_0 1 + r_1 a + dots + r_(n-1)a^(n-1) + a^n = 0$ (все $r_i$ лежат в
  $R$), то элементы $1,a,dots,a^(n-1)$ порождают $R[a]$ как $R$-модуль.

  $#[@cond:integral-finite-subalgebra] =>
  #[@cond:integral-faithful-finite-module]$. Следует рассмотреть модуль
  $M = R[a]$.

  $#[@cond:integral-faithful-finite-module] =>
  #[@cond:integral-monic-equation]$. Пусть $M = sum_(1 <= i <= n) x_i R$. Тогда
  $x_i a = sum_j x_j r_(i j)$, где $r_(i j) in R$. Поэтому
  $sum_j x_j (a delta_(i j) - r_(i j)) = 0$ ($1 <= i <= n$). В силу правила
  Крамера $x_j f(a) = 0$ при всех $j$ и, следовательно, $M f(a) = 0$, где
  $f(T) = det(T delta_(i j) - r_(i j))$. Так как модуль $M$ точен, то
  $f(a) = 0$.
]

#corollary[
  Если $B subset M subset A$ для некоторого конечно порожденного $R$-модуля $M$,
  такого, что $B M subset M$, то подалгебра $B$ алгебры $A$ является целой над
  $R$.
] <cor:finite-stable-module-integrality>
#proof[Если $a in B$, то $M$ — точный $R[a]$-модуль.]

#proposition[
  Пусть $S$ — мультипликативная система в $R$. Если алгебра $A$ целая над $R$,
  то алгебра $S^(-1)A$ целая над $S^(-1)R$.
] <prop:localization-integrality>
#proof[
  Пусть $a slash s in S^(-1)A$ и $r_0 + dots + r_(n-1)a^(n-1) + a^n = 0$, где
  $r_i in R$. Тогда
  $(r_0 slash s^n) + dots + (r_(n-1) slash s)(a slash s)^(n-1) + (a slash
    s)^n = 0$.
]

#proposition[
  Пусть $A$ — коммутативная $R$-алгебра и $M in bold(M)(A)$. Тогда
  #condition-list[
    #condition-item[если $a_1,dots,a_n in A$ — целые элементы над $R$, то
      $R[a_1,dots,a_n] in bold(M)(R)$;] <cond:finite-integral-generators>

    #condition-item[если $A in bold(M)(R)$, то
      $M in bold(M)(R)$.] <cond:finite-algebra-module-restriction>
  ]
] <prop:finite-integral-algebra-generators>
#proof[
  $#[@cond:finite-algebra-module-restriction]$ Если $A = sum_i a_i R$ и
  $M = sum_j b_j A$, то $M = sum_(i j) a_i b_j R$.

  $#[@cond:finite-integral-generators]$ Так как $a_n$ — целый элемент над $R$ и
  заведомо над $R' = R[a_1,dots,a_(n-1)]$, то $R[a_1,dots,a_n] in bold(M)(R')$.
  Проводя индукцию по $n$, убеждаемся, что $R' in bold(M)(R)$. Затем применим
  $#[@cond:finite-algebra-module-restriction]$.
]

#corollary[
  Пусть $A$ — коммутативная $R$-алгебра и $B$ — произвольная $A$-алгебра.
  Множество $R'$ целых над $R$ элементов алгебры $A$ является $R$-подалгеброй в
  $A$. Если $a in A$ — целый элемент над $R'$, то $a in R'$. Если $b in B$ —
  целый элемент над $R'$, то $b$ — целый элемент над $R$.
] <cor:integral-closure-transitivity>
#proof[
  Первое утверждение следует из п. @cond:finite-integral-generators предложения
  @prop:finite-integral-algebra-generators. Что касается третьего утверждения,
  то пусть $c_0 + dots + c_(n-1)b^(n-1) + b^n = 0$, где $c_i in R'$. Тогда в
  силу только #source(104) что упомянутого п. @cond:finite-integral-generators
  $R'' = R[c_0,dots,c_(n-1)] in bold(M)(R)$ и $R''[b] in bold(M)(R'')$, и
  поэтому по п. @cond:finite-algebra-module-restriction
  $R[b] subset R''[b] in bold(M)(R)$. Из @cor:finite-stable-module-integrality
  следует, что $b$ — целый элемент над $R$. Второе утверждение следует из
  третьего при $B = A$.
]

Назовем $R'$ _целым замыканием_ кольца $R$ в $A$. Будем говорить, что область
целостности _целозамкнута_, если она совпадает со своим целым замыканием в ее
поле частных. #idx("целое замыкание кольца")#idx(
  "целозамкнутая область целостности",
)

#proposition[
  Пусть $A subset B$ — коммутативные кольца, причем $B$ является целым над $A$.
  Пусть $frak(p) subset frak(q)$ — простые идеалы кольца $A$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[найдется простой идеал $frak(p)'$ в $B$,
      такой, что
      $frak(p)' inter A = frak(p)$;] <cond:integral-extension-lying-over>

    #condition-item(format: "cyrillic")[для любого такого идеала $frak(p)'$
      найдется простой идеал $frak(q)'$, содержащий $frak(p)'$ и такой, что
      $frak(q)' inter A = frak(q)$;] <cond:integral-extension-going-up>

    #condition-item(format: "cyrillic")[если $frak(p) = frak(q)$, то
      $frak(p)' = frak(q)'$.] <cond:integral-extension-incomparability>
  ]
] <prop:integral-extension-going-up-incomparability>
#proof[
  @cond:integral-extension-lying-over Предположим сначала, что $A$ — локальное
  кольцо с максимальным идеалом $frak(p)$. Если $frak(p)B = B$, то
  $frak(p)B_0 = B_0$ для некоторой конечно порожденной $A$-подалгебры $B_0$ в
  $B$. Из предложения @prop:finite-integral-algebra-generators следует, что
  $B_0 in bold(M)(A)$. Однако $frak(p) subset rad A$, поэтому из
  $frak(p)B_0 = B_0$ следует в силу леммы Накаямы, что $B_0 = 0$, а это
  невозможно. Таким образом, $frak(p)B != B$, и потому найдется максимальный
  идеал $frak(p)'$ в $B$, содержащий $frak(p)B$. Так как
  $frak(p) subset frak(p)' inter A != A$, то $frak(p) = frak(p)' inter A$.

  В общем случае перейдем к $A_(frak(p)) subset B_(frak(p))$ и
  $frak(p)A_(frak(p))$. В силу предложения @prop:localization-integrality
  приведенное выше утверждение можно применить для нахождения простого идеала
  $frak(q)''$ в $B_(frak(p))$, такого, что
  $frak(q)'' inter A_(frak(p)) = frak(p)A_(frak(p))$. Тогда идеал
  $frak(q)' = frak(q)'' inter B$ решает нашу задачу.

  @cond:integral-extension-going-up Перейдем к целому расширению
  $A slash frak(p) subset B slash frak(p)'$ и применим
  @cond:integral-extension-lying-over для нахождения идеала
  $frak(q)' slash frak(p)'$, содержащего $frak(q) slash frak(p)$.

  @cond:integral-extension-incomparability Опять переходя к
  $A slash frak(p) subset B slash frak(p)'$, достаточно показать, что если $A$ и
  $B$ — области целостности и если $frak(q)' != 0$, то $frak(q)' inter A != 0$.
  Если $0 != b in frak(q)'$, то выберем уравнение
  $a_0 + dots + a_(n-1)b^(n-1) + b^n = 0$, где $a_i in A$, минимальной степени.
  Тогда $a_0 in b B inter A subset frak(q)' inter A$ и $a_0 != 0$ (в противном
  случае $a_1 + dots + a_(n-1)b^(n-2) + b^(n-1) = 0$).
]

Последнее означает, что цепи простых идеалов в $B$ не склеиваются при
ограничении на $A$. Таким образом, получили #corollary[
  Отображение $spec(B) arrow.r spec(A)$ сюръективно и $dim B = dim A$.
] <cor:integral-extension-equal-dimension>

#proposition[
  Пусть $R$ — коммутативное нётерово кольцо, $A$ — конечномерная#footnote[Под
    конечномерной $R$-алгеброй понимается $R$-алгебра, являющаяся конечно
    порожденным $R$-модулем. В оригинале употребляется термин «finite
    $R$-algebra». — _Прим. перев. и ред._]#idx("конечномерная алгебра")
  $R$-алгебра и $M in bold(M)(A)$. Тогда эквивалентны следующие условия:
  #condition-list[
    #condition-item[#source(105) длина $A$-модуля $M$
      конечна;] <cond:finite-algebra-module-length>

    #condition-item[длина $R$-модуля $M$
      конечна;] <cond:finite-scalar-module-length>

    #condition-item[носитель $supp(M)$ (в $spec(R)$) является конечным
      множеством и состоит из максимальных
      идеалов.] <cond:finite-maximal-support>
  ]
] <prop:finite-length-support-characterizations>
#proof[
  $#[@cond:finite-algebra-module-length] =>
  #[@cond:finite-scalar-module-length]$. Проводя индукцию по длине, достаточно
  показать, что $R$-длина простого $A$-модуля конечна. Так как
  $M in bold(M)(R)$, то, очевидно (см. предложение
  @prop:finite-integral-algebra-generators
  $#[@cond:finite-scalar-module-length]$), достаточно показать, что идеал
  $ frak(q) = ann_R (M) $
  максимальный, поскольку тогда $M$ является конечномерным пространством над
  $R slash frak(q)$.

  В силу леммы Шура умножение в $M$ на элемент $a in R$ является либо нулевым
  эндоморфизмом, либо автоморфизмом. Это показывает, что идеал $frak(q)$ простой
  и $M$ является векторным пространством над полем частных $F$ кольца
  $R slash frak(q)$. Несложное упражнение — показать, что если $F$ — конечно
  порожденный $R slash frak(q)$-модуль, то $F = R slash frak(q)$.

  $#[@cond:finite-scalar-module-length] => #[@cond:finite-maximal-support]$.
  Если $0 arrow.r M' arrow.r M arrow.r M'' arrow.r 0$ — точная
  последовательность $R$-модулей, то очевидно, что
  $supp(M) = supp(M') union supp(M'')$. Так как наша импликация касается лишь
  $R$-модулей, то, проводя индукцию по длине, достаточно доказать
  $#[@cond:finite-maximal-support]$ для простых $R$-модулей
  $M = R slash frak(m)$, где $frak(m) in maxSpec(R)$. Но тогда
  $supp(M) = {frak(m)}$.

  $#[@cond:finite-maximal-support] => #[@cond:finite-scalar-module-length]$. В
  силу предложения @prop:closed-support-finite-complex $supp(M) = V(frak(a))$,
  где $frak(a) = ann_R (M)$. Положим $R' = R slash frak(a)$. Тогда
  $M in bold(M)(R')$, и поэтому достаточно показать, что кольцо $R'$ артиново.
  Мы знаем, что $spec(R')$ равен $V(frak(a))$ и является конечным множеством
  максимальных идеалов. Положим $J = rad R'$. Из предложения
  @prop:radical-ideal-prime-intersection следует тогда, что $J = nil R'$. Так
  как кольцо $R'$ нётерово, то идеал $J$ нильпотентен. Из китайской теоремы об
  остатках @prop:chinese-remainder-modules в применении к максимальным идеалам
  кольца $R'$ следует, что $R' slash J$ является конечным произведением полей и,
  следовательно, полупростым кольцом. Если $i >= 1$, то $R' slash J$-модуль
  $J^(i-1) slash J^i$ нётеров и, следовательно, его длина конечна. Так как идеал
  $J$ нильпотентен, то кольцо $R'$ артиново, что и требовалось доказать.

  Импликация
  $#[@cond:finite-scalar-module-length] =>
  #[@cond:finite-algebra-module-length]$
  очевидна, поэтому предложение доказано.
]

Двусторонний идеал $frak(p)$ (не обязательно коммутативного) кольца $A$
называется _первичным_, если $a b subset frak(p) => a subset frak(p)$ или
$b subset frak(p)$, где $a$ и $b$ — двусторонние идеалы. Достаточно
рассматривать лишь идеалы $a$ и $b$, содержащие $frak(p)$. Таким образом,
очевидно, что максимальный двусторонний идеал является первичным.
#idx("первичный идеал")

#proposition[
  Пусть $R$ и $A$ такие же, как в предложении
  @prop:finite-length-support-characterizations. Пусть $frak(p)$ — двусторонний
  идеал в $A$. Тогда следующие условия эквивалентны:
  #condition-list[
    #condition-item[#source(106) идеал $frak(p)$
      максимален;] <cond:finite-algebra-maximal-ideal>

    #condition-item[идеал $frak(p)$ первичный и длина $R$-модуля
      $A slash frak(p)$ конечна;] <cond:finite-length-prime-ideal>

    #condition-item[идеал $frak(p)$ является аннулятором в $A$ некоторого
      простого правого $A$-модуля.] <cond:finite-algebra-primitive-ideal>
  ]
] <prop:maximal-primitive-finite-algebra>
#proof[
  $#[@cond:finite-algebra-maximal-ideal] =>
  #[@cond:finite-algebra-primitive-ideal]$. Если $M$ — простой правый
  $(A slash frak(p))$-модуль, то включение $frak(p) subset ann_A (M)$ является
  равенством, поскольку идеал $frak(p)$ максимален.

  $#[@cond:finite-algebra-primitive-ideal] =>
  #[@cond:finite-length-prime-ideal]$. Если $M$ — простой правый $A$-модуль, то
  идеал $frak(p) = ann_A (M)$, очевидно, первичный. В силу предложения
  @prop:finite-length-support-characterizations длина $R$-модуля $M$ конечна, а
  также конечна и длина $R$-модуля $A slash frak(p) subset End_R (M)$.
  #symbol-idx($ann$, sort: "ann", group: "operators", order: 30)

  $#[@cond:finite-length-prime-ideal] => #[@cond:finite-algebra-maximal-ideal]$.
  Длина $R$-модуля $B = A slash frak(p)$ конечна, поэтому кольцо $B$ артиново, а
  нулевой идеал в $B$ является первичным. Последнее означает, что в $B$ нет
  ненулевых нильпотентных идеалов и кольцо $B$ не разлагается в произведение
  ненулевых колец. В силу предложения @prop:artinian-ring-radical-nilpotent
  кольцо $B$ простое, следовательно, идеал $frak(p)$ максимальный, что и
  требовалось доказать.
]

Изучим теперь свойства многочленов. При этом $R$ будет всегда обозначать
коммутативное кольцо, а $t$ — переменную.

#lemma[
  Если старший коэффициент многочлена $P(t) in R[t]$ равен $1$, то найдется
  целое расширение $R'$ кольца $R$, такое, что многочлен $P$ является
  произведением линейных многочленов из $R'[t]$.
] <lem:integral-splitting-algebra>
#proof[
  Индукция по $n = deg(P)$. Очевидно, можно считать, что $n > 1$. Пусть
  $R_1 = R[t] slash (P R[t])$. Ясно, что $R_1 supset R$. Смежный класс $a$
  элемента $t$ в $R_1$ является корнем многочлена $P$. Так как старший
  коэффициент многочлена $P$ равен $1$, то можно применить алгоритм деления.
  Тогда $P(t) = (t - a)Q(t)$ в $R_1[t]$, где $Q$ — многочлен со старшим
  коэффициентом $1$ и степени $n - 1$. По предположению индукции можно вложить
  кольцо $R_1$ в $R'$, над которым многочлен $Q$ разлагается на линейные
  множители.
]

#corollary[
  Пусть $A$ — коммутативная $R$-алгебра, и пусть $R'$ — целое замыкание кольца
  $R$ в $A$. Пусть $P,Q in A[t]$ — многочлены, старшие коэффициенты которых
  равны $1$ и такие, что $P Q in R'[t]$. Тогда $P,Q in R'[t]$.
] <cor:monic-factors-integral-coefficients>
#proof[
  Применим лемму @lem:integral-splitting-algebra для построения кольца $A'$,
  содержащего $A$, в котором многочлены $P$ и $Q$ разлагаются на линейные
  множители: $P = product_i (t - a_i)$, $Q = product_j (t - b_j)$. Пусть $R''$ —
  целое замыкание кольца $R$ в $A'$. Так как $P Q in R'[t]$, то $a_i$ и $b_j$
  лежат в $R''$ (будучи корнями многочлена $P Q$). Следовательно,
  $P,Q in R''[t]$. Так как $R'' inter A = R'$, то следствие доказано.
]

#source(107)
#proposition[
  Пусть $A$ — коммутативная $R$-алгебра и $R'$ — целое замыкание кольца $R$ в
  $A$. Тогда $R'[t]$ — целое замыкание кольца $R[t]$ в $A[t]$.
] <prop:polynomial-integral-closure>
#proof[
  Пусть $B$ — целое замыкание кольца $R[t]$ в $A[t]$. Очевидно, что
  $R'[t] subset B$. Обратно, предположим, что $P in B$. Пусть $P$ — корень
  многочлена
  $ Q(X) = F_0 + dots + F_(m-1)X^(m-1) + X^m in R[t][X]. $
  Выберем натуральное число $r > max(deg(P), deg(F_i))$ ($0 <= i <= m-1$) и
  положим $P_1(t) = P(t) - t^r$. Тогда $P_1$ является корнем многочлена
  $ Q_1(X) = Q(X + t^r) = G_0 + dots + G_(m-1)X^(m-1) + X^m. $
  Таким образом,
  $
    G_0 = -P_1(G_1 + dots + G_(m-1)P_1^(m-2) + P_1^(m-1)).
  $ <eq:integral-polynomial-factor>
  Выбор $r$ гарантирует, что старшие коэффициенты многочленов $-P_1(t)$ и
  $G_0(t) = Q_1(0) = Q(t^r)$ равны $1$. Это ясно для $-P_1$. В случае многочлена
  $ Q(t^r) = F_0(t) + dots + F_(m-1)(t)t^(r(m-1)) + t^(m r) $
  следует лишь заметить, что
  $ deg(F_i (t)t^(r i)) = deg(F_i) + r i < r(i + 1) <= r m "для" i < m. $
  Из уравнения @eq:integral-polynomial-factor следует, что старший коэффициент
  правого множителя также равен $1$. Так как коэффициенты многочлена $G_0$ лежат
  в $R'$, то из следствия @cor:monic-factors-integral-coefficients вытекает, что
  коэффициенты многочлена $-P_1$ и, следовательно, многочлена $P$ также лежат в
  $R'$.
]

#corollary[
  Если $R$ — целозамкнутая область целостности, то $R[t]$ — также целозамкнутая
  область целостности.
] <cor:normal-polynomial-ring>
#proof[
  Пусть $L$ — поле частных кольца $R$. Из предложения
  @prop:polynomial-integral-closure следует, что кольцо $R[t]$ целозамкнуто в
  $L[t]$. Следовательно, остается лишь заметить, что область главных идеалов
  $L[t]$ целозамкнута. Оставляем это в качестве упражнения (см. теорему
  @th:dedekind-domain-characterizations).
]

Закончим этот параграф рядом замечаний о нормах и следах целых элементов.

#proposition[
  Пусть $A$ — коммутативная $R$-алгебра, и пусть $x in M_n (A)$. Элемент $x$
  является целым над $R$ тогда и только тогда, когда коэффициенты его
  характеристического многочлена $P(t) = det(t dot 1 - x)$ являются целыми над
  $R$.
] <prop:integral-matrix-characteristic-polynomial>
#proof[
  Так как $P(x) = 0$ (теорема Кэли — Гамильтона, см. @ch:polynomial-extensions,
  § @sec:endomorphism-characteristic-sequence), то элемент $x$ является целым
  над подалгеброй, порожденной коэффициентами многочлена $P$. Таким #source(108)
  образом, если все эти коэффициенты являются целыми над $R$, то элемент $x$
  также целый над $R$.

  Предположим теперь, что элемент $x$ целый над $R$. Если $e_i$ ($1 <= i <= n$)
  — стандартный базис модуля $A^n$, то $R[x]$-модуль $M$, порожденный элементами
  $e_i$, принадлежит категории $bold(M)(R)$. Пусть $u$ — эндоморфизм модуля
  $A^n$, определенный элементом $x$, и пусть $N subset and.big^n A^n$ есть
  $R$-подмодуль, порожденный всеми элементами вида $m_1 and dots and m_n$, где
  $m_i in M$ ($1 <= i <= n$). Тогда $N in bold(M)(R)$, и подмодуль $N$
  инвариантен относительно $and.big^n u = det(x)$. Так как
  $e_1 and dots and e_n in N$, то $N$ — точный $R[det(x)]$-модуль и потому
  $det(x)$ — целый элемент над $R$.

  Так как элемент $t dot 1 - x in M_n (A[t])$ — целый над $R[t]$, то из
  приведенного выше рассуждения видно, что $P(t)$ — целый элемент над $R[t]$. В
  силу предложения @prop:polynomial-integral-closure коэффициенты многочлена $P$
  целые над $R$, что и требовалось доказать.
]
