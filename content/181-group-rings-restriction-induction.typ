#import "main-defs.typ": (
  Aut, G, K, Tr, U, card, char, hd, idx, moduleCategory, rad, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, numbered-condition,
  proof, proposition, theorem,
)
#import "diagrams/finite-group-induction-basic.typ": (
  induction-pair, restriction-induction-pair, scalar-extension-square,
)

#heading(level: 2)[Групповые кольца, ограничения и индукция]
<sec:group-rings-restriction-induction>

Пусть $R$ — кольцо и $pi$ — полугруппа. Тогда _полугрупповое кольцо_#idx(
  "полугрупповое кольцо",
) (или _групповое кольцо_,#idx("групповое кольцо") если $pi$ — группа)
полугруппы $pi$ над кольцом $R$ определяется как свободный $R$-модуль с базисом
$pi$ и с умножением, продолжающим по $R$-билинейности умножение в $pi$. Тем
самым получаем функтор от $R$ и от $pi$. Именно, если $f: R -> R'$ — гомоморфизм
колец и $j: pi -> pi'$ — гомоморфизм полугрупп, то рассмотрим
$f: R pi -> R' pi$, полагая $f (sum_(x in pi) a_x x) = sum_(x in pi) f (a_x) x$,
и $j: R pi -> R pi'$, полагая
$j (sum_(x in pi) a_x x) = sum a_x j (x)$
(см. @ch:stable-projective-structure, §~@sec:free-products-firs-cohns-theorem).
Если $pi' = {1}$, то получаем _пополнение_#idx("пополнение") $R pi -> R$, где
$sum a_x x arrow.r.bar sum a_x$. Ядро $I$ этого гомоморфизма называется _идеалом
пополнения_#idx("идеал пополнения") (_фундаментальным идеалом_).#idx(
  "фундаментальный идеал",
) Это двусторонний идеал, порожденный как $R$-модуль всеми элементами $1-x$, где
$x in pi$. Пополнение определяет структуру $R pi$-модуля на $R$ ($pi$ действует
тривиально). Этот модуль назовем _тривиальным $R pi$-модулем_#idx(
  "тривиальный Rπ-модуль",
) и обозначим его через $R_pi$.

Если $pi'$ — подгруппа группы $pi$, то через $[pi:pi']$ обозначим индекс
подгруппы $pi'$ в $pi$. Выражение «$pi$ является $p$-группой» всегда будет
означать, что $p$ — простое число и порядок каждого элемента группы $pi$
является степенью числа $p$. Если $pi$ — конечная группа, то это эквивалентно
тому, что $[pi:1]$ является степенью числа $p$.

#source(428)
#proposition(title: [Машке])[
  #idx("теорема Машке")
  Пусть $pi$ — группа и $pi'$ — подгруппа конечного индекса $n=[pi:pi']$. Пусть
  $R$ — кольцо и $n in U (R)$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[Точная последовательность $R pi$-модулей
      $ 0 -> M' -> M arrow.r^p M'' -> 0 $
      расщепляется, если она расщепляется как последовательность
      $R pi'$-модулей.] <cond:maschke-relative-splitting>

    #condition-item(format: "cyrillic")[Если $M in moduleCategory-R pi$, то
      $hd_(R pi) (M)=hd_(R pi') (M)$.] <cond:maschke-projective-dimension>
  ]
] <prop:maschke-relative-splitting>

#proof[
  @cond:maschke-relative-splitting Пусть $h: M'' -> M$ — $R pi'$-гомоморфизм,
  такой, что $p h=1_(M'')$. Пусть $pi=union pi' x_i$ $(1 <= i <= n)$ —
  разложение группы $pi$ на смежные классы и $h' (m)=sum h (m x_i^(-1)) x_i$
  $(1 <= i <= n)$. Так как отображение $h$ является $pi'$-линейным, то
  $h (m x_i^(-1)) x_i$ зависит лишь от смежного класса $pi' x_i$. Если
  $x in pi$, то
  $
    h' (m x)=sum h (m x x_i^(-1)) x_i
    =(sum h (m x x_i^(-1)) x_i x^(-1)) x=h' (m) x,
  $
  поскольку $x_i x^(-1)$ также образуют множество представителей смежных
  классов. Следовательно, отображение $h'$ является $pi$-линейным. Кроме того,
  $p h' (m)=sum_i p h (m x_i^(-1)) x_i=sum_i m x_i^(-1) x_i=m dot n$. Итак,
  $n^(-1) h'$ является $R pi$-линейным отображением и правым обратным для $p$.

  @cond:maschke-projective-dimension Если $pi=union x_i pi'$ $(1 <= i <= n)$, то
  очевидно, что $R pi=union.sq.big x_i R pi'$. Поэтому $R pi$ является свободным
  $R pi'$-модулем. Следовательно, если $M in moduleCategory-R pi$, то
  $R pi$-проективная резольвента модуля $M$ является также $R pi'$-проективной
  резольвентой. Поэтому $hd_(R pi') (M) <= hd_(R pi) (M)$. Обратно, предположим,
  что $hd_(R pi') (M)=n < infinity$. Выберем точную последовательность
  $ 0 -> P_n -> dots -> P_0 -> M -> 0 $
  в категории $moduleCategory-R pi$ с $R pi$-проективными модулями $P_i$
  $(0 <= i < n)$. Нам надо показать, что модуль $P_n$ является
  $R pi$-проективным, если он $R pi'$-проективен. Но это следует из части
  @cond:maschke-relative-splitting, если взять $P_n$ вместо $M''$. Предложение
  доказано.
]

#theorem(word: "Следствие")[
  Пусть $pi$ — конечная группа порядка $n=[pi:1]$. Пусть $R$ — целозамкнутая
  область целостности с полем частных $L$, характеристика которого не делит $n$.
  Тогда алгебра $L pi$ полупроста и каждый $R$-порядок в $L pi$, содержащий
  $R pi$, содержится в $n^(-1) R pi$.
] <th:maschke>

#proof[
  Первое утверждение следует непосредственно из @prop:maschke-relative-splitting
  @cond:maschke-relative-splitting (см. @th:semisimple-ring-characterizations).
  Пусть $pi={x_1=1,x_2,dots,x_n}$. #source(429)Регулярное представление алгебры
  $L pi$ в этом базисе сопоставляет каждому элементу $x_i != 1$ матрицу
  перестановки с нулевыми диагональными элементами. Следовательно,
  $Tr_(L pi slash L) (x_i)=delta_(1 i) dot n$ ($delta_(i j)$ — символ
  Кронекера). Таким образом, если $x'_i=n^(-1) x_i^(-1)$, то
  $Tr_(L pi slash L) (x_i x'_j)=delta_(i j)$ $(1 <= i,j <= n)$. Пусть $B$
  является $R$-порядком в $L pi$, содержащим $R pi$. Пусть $b in B$. Ясно, что
  элементы $x'_1,dots,x'_n$ образуют $L$-базис в $L pi$. Поэтому можно записать
  $b=sum x'_j b_j$ $(b_j in L)$. Тогда
  $Tr_(L pi slash L) (x_i b)=sum_j Tr_(L pi slash L) (x_i x'_j) b_j=b_i$. Но
  элемент $x_i b in B$ целый над $R$. Поэтому из
  @prop:integral-matrix-characteristic-polynomial следует, что
  характеристический многочлен $L$-эндоморфизма $L pi arrow.r^(x_i b dot) L pi$
  таков, что его коэффициенты являются целыми над $R$. Так как кольцо $R$
  целозамкнуто, то они лежат в $R$. В частности,
  $b_i=Tr_(L pi slash L) (x_i b) in R$. Итак, $B subset sum x'_j R=n^(-1) R pi$,
  что и требовалось доказать.
]

Покажем теперь, что происходит в другом экстремальном случае, когда
$char (L)=p > 0$ и $pi$ является $p$-группой.

#proposition[
  Пусть $pi$ — конечная $p$-группа, действующая на конечном множестве $S$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[
      $card (S^pi) equiv card (S) mod p$, где $S^pi$ — это множество неподвижных
      точек группы $pi$;
    ] <cond:p-group-fixed-point-congruence>

    #condition-item(format: "cyrillic")[группа $pi$ нильпотентна.]
    <cond:finite-p-group-nilpotence>
  ]
] <prop:finite-p-group-fixed-points>

#proof[
  @cond:p-group-fixed-point-congruence Если $s in S$, то пусть
  $pi_s={x in pi | x s=s}$ (стабильная подгруппа). Тогда отображение
  $x arrow.r.bar x s$ индуцирует биективное отображение $pi slash pi_s -> pi s$
  (в орбиты). Поэтому $card (pi s)=[pi:pi_s]$ является положительной степенью
  числа $p$, кроме того случая, когда $s in S^pi$. Так как $S$ — дизъюнктное
  объединение орбит, то $card (S)=card (S^pi)+N$, где $N$ — сумма положительных
  степеней числа $p$.

  @cond:finite-p-group-nilpotence Пусть $pi$ действует на множестве $pi$ путем
  сопряжения. Тогда $pi^pi$ совпадает с центром группы $pi$, при этом число
  элементов в нем сравнимо с $[pi:1]$ по модулю $p$. Применяя индукцию по
  $[pi:1]$ и переходя к факторгруппе группы $pi$ по ее центру, получаем
  @cond:finite-p-group-nilpotence.
]

#corollary[
  Пусть $R$ — коммутативное локальное кольцо с полем вычетов $k$, характеристика
  которого равна $p > 0$. Пусть $pi$ — конечная $p$-группа. Тогда $R pi$ —
  локальное кольцо с единственным простым модулем $k_pi$.
] <cor:local-p-group-ring>

#proof[
  Пусть $frak(m)=rad R$, так что $k=R slash frak(m)$. Тогда
  $frak(m) (R pi) subset rad R pi$ (см. @cor:finite-algebra-base-radical).
  Поэтому нам достаточно показать, что кольцо $R pi slash frak(m) (R pi)=k pi$
  локально. #source(430)Но $k_pi=k pi slash I$, где $I$ — фундаментальный идеал.
  Если мы покажем, что $k_pi$ — единственный простой модуль, то тогда будет
  ясно, что $I subset rad k pi$. В таком случае $I=rad k pi$ и является
  нильпотентным идеалом, а кольцо $k pi$ локально. Последнее условие не меняется
  при расширениях основного поля. Поэтому достаточно проверить его выполнение
  для простого подполя $k_0 subset k$.

  Пусть $M != 0$ — простой $k_0 pi$-модуль. Тогда $M$ — конечное множество.
  Поэтому из предложения @prop:finite-p-group-fixed-points вытекает, что
  $card (M^pi) equiv card (M) mod p$. Так как $card (M)$ является положительной
  степенью числа $p$, то $M^pi != 0$. Таким образом, так как $M^pi$ является
  $k_0 pi$-подмодулем, а $M$ — простой модуль, то $M^pi=M tilde.eq (k_0)_pi$.
  Доказательство завершено.
]

_Начиная с этого момента, $R$ — коммутативное кольцо._ Пусть $j: pi' -> pi$ —
гомоморфизм групп. Тогда получаем функторы _индукции_#idx("функтор индукции") и
_ограничения_#idx("функтор ограничения")
$ #induction-pair("group") $
Если $f: R' -> R$ — гомоморфизм коммутативных колец, то также получаем функторы
$ #induction-pair("ring") $
Согласованность этих функторов выражается следующими естественными
изоморфизмами, возникающими из коммутативной диаграммы
$ #scalar-extension-square() $

#numbered-condition[
  $f_* j_* tilde.eq j_* f_*$: если $M in moduleCategory-R' pi'$, то
  $(M tensor_(R' pi') R' pi) tensor_(R') R tilde.eq
  M tensor_(R' pi') R pi tilde.eq (M tensor_(R') R) tensor_(R pi') R pi$, как
  $R pi$-модули.
] <eq:group-induction-scalar-extension>

#numbered-condition[
  $j_* f^* tilde.eq f^* j_*$: если $M in moduleCategory-R pi'$, то
  $(f^* M) tensor_(R' pi') R' pi tilde.eq
  f^* (M tensor_(R pi') R pi)$, как $R' pi$-модули.
] <eq:group-induction-scalar-restriction>

#numbered-condition[
  $f_* j^*=j^* f_*$: если $M in moduleCategory-R' pi$, то
  $j^* M tensor_(R') R=j^* (M tensor_(R') R)$, как $R pi'$-модули.
] <eq:group-restriction-scalar-extension>

#numbered-condition[
  $f^* j^*=j^* f^*$: если $M in moduleCategory-R pi$, то $f^* j^* M=j^* f^* M$
  как $R' pi'$-модули.
] <eq:group-restriction-scalar-restriction>

В @eq:group-restriction-scalar-extension и
@eq:group-restriction-scalar-restriction изоморфизмы являются равенствами. В
@eq:group-induction-scalar-restriction отображение
$M tensor_(R' pi') R' pi -> M tensor_(R pi') R pi$ определено так:
$m tensor x arrow.r.bar m tensor x$ $(m in M,x in pi)$. Существование
изоморфизма в @eq:group-induction-scalar-extension мы можем вывести из
ассоциативности тензорных произведений, как только мы отметили естественный
изоморфизм $M tensor_(R') R tilde.eq
#source(431)M tensor_(R' pi) R pi$ для модуля $M in moduleCategory-R pi$ и
аналогичное свойство для группы $pi'$. Подобным же образом, если $f': R'' -> R'$
— другой гомоморфизм колец и $j': pi'' -> pi'$ — другой гомоморфизм групп, то
получаем формулы транзитивности
$ (j j')_* tilde.eq j_* j'_*, quad (j j')^*=(j')^* j^*, $
$ (f f')_* tilde.eq f_* f'_*, quad (f f')^*=(f')^* f^*. $
Для ограничения они являются равенствами. Для индукции они соответствуют
ассоциативности тензорных произведений.

Далее введем аддитивный бифунктор
$
  tensor_R: (moduleCategory-R pi) times (moduleCategory-R pi)
  -> moduleCategory-R pi.
$
Если $M,N in moduleCategory-R pi$, то $M tensor_R N$ является $R$-модулем, на
котором группа $pi$ действует так: $(m tensor n) x=m x tensor n x$ для
$M,N in moduleCategory-R pi$. Распространим это действие по $R$-линейности на
$R pi$. Очевидно, что естественный изоморфизм
$M tensor_R N tilde.eq N tensor_R M$ является изоморфизмом $R pi$-модулей.
Заметим также, что отображение
$ M tensor_R R_pi tilde.eq M $
является изоморфизмом $R pi$-модулей.

#proposition(title: [«взаимность Фробениуса»])[
  #idx("взаимность Фробениуса")
  Пусть $R$ — коммутативное кольцо и $j: pi' -> pi$ — гомоморфизм групп. Если
  $M in moduleCategory-R pi$ и $N in moduleCategory-R pi'$, то существует
  изоморфизм
  $ phi: j_* (j^* M tensor_R N) -> M tensor_R j_* N, $
  который задан так:
  $
    phi ((m tensor n) tensor x)=m x tensor (n tensor x)
    quad (m in M,n in N,x in pi).
  $
  Этот изоморфизм определяет изоморфизм функторов
  $ (moduleCategory-R pi) times (moduleCategory-R pi') -> moduleCategory-R pi. $
] <prop:frobenius-reciprocity>

#proof[
  Пусть $W=M tensor_R j_* N=M tensor_R (N tensor_(R pi') R pi)$. Если $x in pi$,
  то выражение $m x tensor (n tensor x) in W$ $R$-билинейно по
  $(m,n) in M times N$. Поэтому оно определяет $R$-линейное отображение
  $h_x: M tensor_R N -> W$. Так как $R pi$ является свободным $R$-модулем с
  базисом $pi$, то можно, используя отображения $h_x$, определить $R$-линейное
  отображение $phi': (M tensor_R N) tensor_R R pi -> W$, для которого
  $phi' ((m tensor n) tensor x)=m x tensor (n tensor x)$. Если $y in pi'$, то
  $phi' ((m tensor n) tensor j (y) x)=m j (y) x tensor (n tensor j (y) x)
  =m j (y) x tensor (n y tensor x)$, в то время как
  $phi' ((m tensor n) y tensor x)=phi' ((m j (y) tensor n y) tensor x)
  =m j (y) x tensor (n y tensor x)$. Таким образом, отображение $phi'$ является
  $R pi'$-билинейным. Поэтому оно индуцирует гомоморфизм
  $phi: (M tensor_R N) tensor_(R pi') R pi -> W$. Если $y in pi$, то
  $phi (((m tensor n) tensor x) y)=phi ((m tensor n) tensor x y)
  =m x y tensor (n tensor x y)
  #source(432)=m x y tensor ((n tensor x) y)
  =(m x tensor (n tensor x)) y=phi ((m tensor n) tensor x) y$. Поэтому
  отображение $phi$ является $R pi$-линейным.

  Для построения обратного отображения пусть $m in M$, $n in N$ и $x in pi$.
  Если $V=(M tensor_R N) tensor_(R pi') R pi$, то выражение
  $(m x^(-1) tensor n) tensor x in V$ определяет $R$-линейное отображение
  $N -> V$. Если $m$ зафиксировано, а $x$ пробегает группу $pi$, то получаем
  $R$-линейное отображение $h'_m: N tensor_R R pi -> V$. Если $y in pi'$, то
  $h'_m (n tensor j (y) x)
  =(m x^(-1) j (y)^(-1) tensor n) tensor j (y) x
  =(m x^(-1) j (y)^(-1) tensor n) y tensor x
  =(m x^(-1) tensor n y) tensor x=h'_m (n y tensor x)$. Следовательно, $h'_m$
  индуцирует $R$-линейное отображение $h_m: N tensor_(R pi') R pi -> V$, для
  которого $h_m (n tensor x)=(m x^(-1) tensor n) tensor x$. Так как это
  выражение $R$-линейно по $m$, то получим отображение
  $psi: M tensor_R (N tensor_(R pi') R pi) -> V$, для которого
  $psi (m tensor (n tensor x))=(m x^(-1) tensor n) tensor x$. Очевидно, что
  $psi$ является обратным отображением для $phi$. Поэтому $phi$ — изоморфизм.

  Допустим, что $f: M -> M_1$ — морфизм в категории $moduleCategory-R pi$, а
  $g: N -> N_1$ — морфизм в категории $moduleCategory-R pi'$. Тогда
  $phi compose ((f tensor_R g) tensor_(R pi') R pi)$ переводит
  $(m tensor n) tensor x$ в $f (m) x tensor (g (n) tensor x)$, в то время как
  $(f tensor_R (g tensor_(R pi') R pi)) compose phi$ переводит этот элемент в
  $f (m x) tensor (g (n) tensor x)$. Так как отображение $f$ является
  $pi$-линейным, эти два образа равны. Таким образом, $phi$ — естественное
  преобразование. Предложение доказано.
]

#corollary[
  Если модуль $M in moduleCategory-R pi$, рассматриваемый как $R$-модуль,
  обозначить через $j^* M$, то отображение
  $ M tensor_R R pi tilde.eq j^* M tensor_R R pi $
  оказывается изоморфизмом $R pi$-модулей.
] <cor:diagonal-regular-tensor-isomorphism>

#proof[
  Пусть $j$ — вложение тривиальной подгруппы. Применим предложение
  @prop:frobenius-reciprocity с $N=R$.
]

Через
$ bold(M)_0 (R pi) $
обозначим полную подкатегорию всех модулей $M in moduleCategory-R pi$, которые
как $R$-модули конечно порождены и проективны.

#corollary[
  Тензорное произведение индуцирует функторы
  $ tensor_R: bold(M)_0 (R pi) times bold(M)_0 (R pi) -> bold(M)_0 (R pi) $
  и
  $ tensor_R: bold(M)_0 (R pi) times italic(P) (R pi) -> italic(P) (R pi), $
  сохраняющие короткие точные последовательности по каждому аргументу.
] <cor:group-ring-projective-tensor-functors>

#proof[
  Сохранение точности очевидно, поскольку короткие точные последовательности в
  категории $italic(P)$ #source(433)расщепляются, а в $bold(M)_0$ они
  расщепляются как последовательности $R$-модулей. Кроме того, ясно, что
  $M tensor_R N in bold(M)_0$, если $M,N in bold(M)_0$. Если к тому же
  $P in italic(P)$, то остается показать, что $M tensor_R P in italic(P)$.
  Рассуждения с прямыми суммами сводят нашу задачу к случаю $P=R pi$, где это
  уже непосредственно вытекает из @cor:diagonal-regular-tensor-isomorphism.
  Следствие доказано.
]

#definition[
  Пусть $R$ — коммутативное кольцо и $pi$ — группа. Положим
  $ G_R (pi)=K_0 (bold(M)_0 (R pi)). $
] <def:group-ring-frobenius-functor>

В силу @cor:group-ring-projective-tensor-functors можно, используя $tensor_R$,
наделить группу $G_R (pi)$ структурой _коммутативного кольца_. Даже более того,
если $P in italic(P) (R)$ и $M in bold(M)_0 (R pi)$, то
$P tensor_R M in bold(M)_0 (R pi)$. Используя это, можем рассматривать
$G_R (pi)$ как $K_0 (R)$-алгебру. Единичный элемент в группе $G_R (pi)$ равен
$[R_pi]$. Будем называть группы
$ K_i (bold(M)_0 (R pi)) quad (i=0,1) $
и
$ K_i (italic(P) (R pi))=K_i (R pi) quad (i=0,1) $
четырьмя _базисными $G_R$-модулями_.#idx("базисные G_R-модули") Они
действительно являются $G_R (pi)$-модулями, причем операции определяются
равенствами
$ [M] [N]=[M tensor_R N] quad (i=0) $
и
$ [M] [N,alpha]=[M tensor_R N,M tensor_R alpha] quad (i=1), $
где $M in bold(M)_0$, а $N$ лежит в $bold(M)_0$ или, что также возможно, в
$italic(P)$ и $alpha in Aut_(R pi) (N)$. Наши обозначения должны наводить на
мысль рассматривать $G_R$ и базисные $G_R$-модули для фиксированного кольца $R$
как функторы от группы $pi$. Точный смысл этой функториальности будет описан в
следующем ниже предложении @prop:group-ring-induction-restriction. Сначала,
однако, покажем, как категория $bold(M)_0 (R pi)$ связана в некоторых случаях с
категорией $bold(M) (R pi)$.

#proposition[
  Пусть $R$ — коммутативное регулярное кольцо и $pi$ — конечная группа. Тогда
  $italic(P) (R pi) subset bold(M)_0 (R pi) subset bold(M) (R pi)$, и последнее
  включение индуцирует изоморфизмы
  $ K_i (bold(M)_0 (R pi)) -> K_i (bold(M) (R pi))=G_i (R pi) quad (i=0,1). $
  В частности, $G_R (pi)=G_0 (R pi)$.
] <prop:regular-group-ring-resolution>

#proof[
  Если $P in italic(P) (R pi)$, то $P in bold(M)_0 (R pi)$, поскольку $R pi$
  является свободным $R$-модулем конечного ранга ($[pi:1]$). Второе вложение
  очевидно.

  Пусть $M in bold(M) (R pi)$. Так как $pi$ — конечная группа, то $M$ также
  является конечно порожденным $R$-модулем. Поэтому #source(
    434,
  )$hd_R (M)=n < infinity$. Пусть
  $ 0 -> P_n -> P_(n-1) -> dots -> P_0 -> M -> 0 $
  является точной последовательностью $R pi$-модулей, где
  $P_i in italic(P) (R pi)$ $(0 <= i < n)$. (Заметим, что кольцо $R pi$ нётерово
  справа, и мы можем сделать это допущение.) Тогда, так как $P_i$ принадлежат
  также $italic(P) (R)$ $(0 <= i < n)$, $P_n in italic(P) (R)$, т. е.
  $P_n in bold(M)_0 (R pi)$. Но теперь можно применить
  @th:projective-resolution-k-isomorphisms и показать, что отображения
  $K_i (bold(M)_0) -> K_i (bold(M))$ $(i=0,1)$ оказываются изоморфизмами, что и
  требовалось показать.
]

#proposition[
  Пусть $R$ — коммутативное кольцо и $pi$ — конечная группа. Пусть
  $j: pi' -> pi$ — вложение подгруппы конечного индекса. Тогда ограничение и
  индукция индуцируют точные функторы
  $ #restriction-induction-pair("relative-projective") $
  и
  $ #restriction-induction-pair("projective") $
  Следовательно, если $K_R$ — любой из базисных $G_R$-модулей, то получаем
  индуцированные аддитивные отображения
  $ #restriction-induction-pair("k") $
  Они удовлетворяют следующим условиям:

  #condition-list[
    #condition-item[
      $j^*: G_R (pi) -> G_R (pi')$ является гомоморфизмом колец, а отображение
      $j^*: K_R (pi) -> K_R (pi')$ оказывается $j^*$-полулинейным, т. е.
      $j^* (a b)=j^* (a) j^* (b)$ для $a in G_R (pi),b in K_R (pi)$.
    ] <cond:group-restriction-semilinearity>

    #condition-item[
      Если $a in G_R (pi),a' in G_R (pi'),b in K_R (pi)$ и $b' in K_R (pi')$, то
      $ a dot j_* b'=j_* (j^* a dot b') $
      и
      $ j_* a' dot b=j_* (a' dot j^* b). $
    ] <cond:group-induction-reciprocity>
  ]
] <prop:group-ring-induction-restriction>

#proof[
  Очевидно, что ограничение сохраняет принадлежность категории $bold(M)_0$ и что
  индукция сохраняет принадлежность категории $italic(P)$. Другие два
  утверждения легко следуют из того, что $R pi in italic(P) (R pi')$. (На самом
  деле $R pi$ — свободный $R pi'$-модуль с базисом, состоящим из представителей
  смежных классов.) Последнее влечет за собой, что функторы $j_*$ и $j^*$,
  очевидно, точны. Следовательно, мы получаем нужные гомоморфизмы. Так как $j^*$
  сохраняет $tensor_R$ (что очевидно), то @cond:group-restriction-semilinearity
  немедленно следует из определения действия функтора $G_R$ на $K_R$. Аналогично
  @cond:group-induction-reciprocity #source(435)непосредственно вытекает из
  фробениусовой взаимности (см. @prop:frobenius-reciprocity) в том случае, когда
  $K_R$ — один из функторов $K_0$. Это же рассуждение применимо и к функторам
  $K_1$ в силу естественности изоморфизма фробениусовой взаимности. Именно,
  пусть в ситуации предложения @prop:frobenius-reciprocity
  $alpha in Aut_(R pi) (M)$ и $beta in Aut_(R pi') (N)$. Тогда отображение
  $
    phi: (j_* (j^* M tensor_R N),j_* (j^* alpha tensor_R beta))
    -> (M tensor_R j_* N,alpha tensor_R j_* beta)
  $
  оказывается изоморфизмом в категории $Sigma (moduleCategory-R pi)$
  автоморфизмов $R pi$-модулей. Полагая $alpha$ и $beta$ равными тождественным
  преобразованиям, приходим к двум формулам из
  @cond:group-induction-reciprocity, где в качестве $K_R$ взят функтор $K_1$,
  что и требовалось.
]

#proposition[
  В ситуации предложения @prop:group-ring-induction-restriction пусть
  $f: R' -> R$ — гомоморфизм коммутативных колец. Тогда
  $f_*: moduleCategory-R' pi -> moduleCategory-R pi$ сохраняет тензорные
  произведения в том смысле, что существует естественный изоморфизм
  $ f_* (M tensor_(R') N) tilde.eq f_* M tensor_R f_* N $
  $R pi$-модулей, где $M,N in moduleCategory-R' pi$. Кроме того, $f_*$
  индуцирует точные функторы $bold(M)_0 (R' pi) -> bold(M)_0 (R pi)$ и
  $italic(P) (R' pi) -> italic(P) (R pi)$, а также аддитивные отображения
  $ f_*: G_(R') (pi) -> G_R (pi) quad "и" quad f_*: K_(R') (pi) -> K_R (pi). $
  Первое из них является гомоморфизмом колец, а второе полулинейно относительно
  первого, т. е. $f_* (a b)=f_* (a) f_* (b)$ для
  $a in G_(R') (pi),b in K_(R') (pi)$. Кроме того, если $j: pi' -> pi$, как и в
  @prop:group-ring-induction-restriction, то $f_* j_*=j_* f_*$ и
  $f_* j^*=j^* f_*$.

  Если же $R$ — конечно порожденный проективный $R'$-модуль (т. е.
  $R in italic(P) (R')$), то функтор ограничения
  $f^*: moduleCategory-R pi -> moduleCategory-R' pi$ индуцирует функторы
  $bold(M)_0 (R pi) -> bold(M)_0 (R' pi)$ и
  $italic(P) (R pi) -> italic(P) (R' pi)$ и, следовательно, аддитивное
  отображение
  $ f^*: K_R (pi) -> K_(R') (pi). $
  Отображения $f^*$ также перестановочны с $j_*$ и $j^*$, при этом $f^* f_*$
  совпадает с умножением на $[R]_(R')$, т. е. на класс $R'$-модуля $R$ в группе
  $K_0 (R')$ (или на класс тривиального $R' pi$-модуля в группе $G_(R') (pi)$).
] <prop:group-ring-scalar-extension-restriction>

#proof[
  Заметим, что
  $
    f_* M tensor_R f_* N=(M tensor_(R') R) tensor_R (N tensor_(R') R)
    tilde.eq M tensor_(R') (N tensor_(R') R) tilde.eq f_* (M tensor_(R') N).
  $
  При этом отображения, как легко видеть, являются $R pi$-изоморфизмами. Ясно
  (из определений), что $f_*$ сохраняет принадлежность категориям $bold(M)_0$ и
  $italic(P)$. Его ограничения на эти категории являются #source(436)точными
  функторами, поскольку короткие точные последовательности в $bold(M)_0 (R' pi)$
  и $italic(P) (R' pi)$ расщепляются над $R'$. Полулинейность преобразования
  $f_*$ следует из сохранения тензорных произведений. Перестановочность $f_*$ (и
  $f^*$) с $j_*$ и $j^*$ была установлена перед предложением
  @prop:frobenius-reciprocity.

  Если $R in italic(P) (R')$, то $P in italic(P) (R')$ для всех
  $P in italic(P) (R)$. Таким образом,
  $f^* bold(M)_0 (R pi) subset bold(M)_0 (R' pi)$. Аналогично
  $R pi in italic(P) (R' pi)$, и поэтому
  $f^* italic(P) (R pi) subset italic(P) (R' pi)$. Если
  $M in moduleCategory-R' pi$, то $f^* f_* M=f^* (M tensor_(R') R)
  tilde.eq M tensor_(R') R$, где мы рассматриваем $R$ как $R'$-модуль или как
  $R' pi$-модуль с тривиальным действием группы $pi$. Это завершает
  доказательство.
]
