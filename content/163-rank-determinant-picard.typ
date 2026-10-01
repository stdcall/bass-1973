#import "main-defs.typ": (
  Aut, E, End, GL, H, Im, K, Ker, Pic, PicCat, Rk, SK, SL, U, ann, det, idx,
  maxSpec, moduleCategory, rad, rk, source, spec, supp, symbol-idx, tensor,
  transpose,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, lemma, numbered-condition, proof,
  proposition, theorem,
)
#import "diagrams/projective-k-theory-determinant.typ": (
  determinant-exact-sequences, determinant-naturality, picard-quotient-triangle,
)

#heading(level: 2)[Ранг: отображения $K_0 -> H_0$ и
  $det: bold(P) -> PicCat$] <sec:rank-determinant-picard>
#symbol-idx($det$, sort: "det", group: "operators", order: 40)

В этом параграфе _все кольца будут предполагаться коммутативными_.

Пусть $A$ — коммутативное кольцо и $X = spec(A)$. Из гл.~@ch:rings-modules,
§~@sec:chain-conditions-spectrum-dimension мы знаем, что пространство $X$
квазикомпактно, а структура открыто-замкнутых подмножеств в $X$ изоморфна
относительно отображения $e arrow.r.bar supp(e A)$ структуре идемпотентов
$e in A$ (@prop:idempotents-clopen-spectrum). Введем теперь множество
$ H_0 (A) = {"непрерывные функции": spec(A) -> ZZ}, $
где кольцо $ZZ$ наделено дискретной топологией. Если $r in H_0 (A)$, то из
квазикомпактности следует, что функция $r$ ограничена, т. е. принимает лишь
конечное число значений. Таким образом, $X_n = r^(-1){n}$ — непересекающиеся
открытые множества, почти все из которых пустые и объединение которых равно $X$.
Если $e_n$ — идемпотент, для которого $X_n = supp(e_n A)$, то идемпотенты $e_n$
ортогональны, почти все равны нулю и $1 = sum_n e_n$.

Гомоморфизм колец $f: A -> B$ индуцирует непрерывное отображение
$#transpose($f$, mark: $a$): spec(B) -> spec(A)$,
$#transpose($f$, mark: $a$) (frak(p)) = f^(-1)(frak(p))$, и, следовательно,
гомоморфизм колец $H_0 (f): H_0 (A) -> H_0 (B)$. Из сделанного выше замечания
сразу же следует

#lemma[
  Отображение $H_0 (f): H_0 (A) -> H_0 (B)$ инъективно тогда и только тогда,
  когда $Ker(f)$ не содержит ненулевых идемпотентов. Оно сюръективно тогда и
  только тогда, когда каждое множество ортогональных идемпотентов кольца $B$
  поднимается до такого же множества в кольце $A$.
] <lem:rank-function-base-change>

В силу @th:projective-local-free-rank $[P: A] in H_0 (A)$ для $P in bold(P)(A)$.
Из @th:projective-local-free-rank вытекает, что мы получаем индуцированный
гомоморфизм колец, #source(359)называемый _рангом_#idx("ранг"):
$ rk: K_0 (A) -> H_0 (A). $#symbol-idx(
  $rk$,
  sort: "rk",
  group: "operators",
  order: 69,
)
Положим
$ Rk_0 (A) = Ker(rk). $#symbol-idx(
  $Rk_0$,
  sort: "Rk_0",
  group: "operators",
  order: 70,
)
Элементы этой группы имеют вид $[P] - [Q]$, где $[P: A] = [Q: A]$. Из
@prop:projective-base-change-rank следует, что $rk$ является естественным
преобразованием, и, следовательно, $Rk_0 (A)$ — ковариантный функтор по $A$.

Построим теперь (естественное) правое обратное отображение
$epsilon: H_0 (A) -> K_0 (A)$ для $rk$. Если $e^2 = e$ в кольце $A$, то через
$r_e$ обозначим характеристическую функцию подмножества $supp(e A)$. Эти функции
аддитивно порождают $H_0 (A)$. Мы хотим определить
$ epsilon(sum n_i r_(e_i)) = sum n_i [e_i A]. $
Рассуждения, используемые в теории интегрирования, и показывающие, что
аналогичное определение интеграла ступенчатых функций корректно, и в нашем
случае обеспечивают корректность определения отображения $epsilon$, являющегося
гомоморфизмом колец. Кроме того, $rk[e A] = r_e$. Поэтому $epsilon$ является
правым обратным для $rk$. Если $f: A -> B$ — гомоморфизм, то $H_0 (f)$ переводит
$r_e$ в $r_(f(e))$, а отображение $K_0 (A) -> K_0 (B)$ переводит $[e A]_A$ в
$[f(e) B]_B$. Таким образом, $epsilon$ — естественное преобразование. Подводя
итог изложенному, получаем

#proposition[
  Точная последовательность
  $ 0 -> Rk_0 (A) -> K_0 (A) arrow.r^rk H_0 (A) -> 0 $
  естественна по $A$. Она расщепляется с помощью гомоморфизма колец
  $epsilon: H_0 (A) -> K_0 (A)$, который также естествен, а его образ
  порождается аддитивно всеми элементами $[e A]$, где $e$ — идемпотент кольца
  $A$.
] <prop:projective-rank-split-exact-sequence>

Далее будем рассматривать $PicCat(A)$ как категорию с произведением $(tensor_A)$
в смысле гл.~@ch:exact-k-sequences. Очевидно, что
$ K_0 PicCat(A) = Pic(A). $
Если $P in PicCat(A)$, то $End_A (P) = A$. Следовательно, $Aut_A (P) = U(A)$
(как абелевы группы). Объект $A$ кофинален в категории $PicCat(A)$. Поэтому в
силу @cor:whitehead-cofinal-full-subcategory
$ K_1 PicCat(A) = U(A). $
Если $f: A -> B$ — гомоморфизм колец, то функтор
$tensor_A B: PicCat(A) -> PicCat(B)$ сохраняет произведение и кофинален. Кроме
того, он Е-сюръективен, поскольку это условие требует возможности поднимать
автоморфизмы по коммутанту, а все группы автоморфизмов в категории $PicCat$
абелевы. Аналогично если $frak(q) subset frak(q)'$ — #source(360)идеалы кольца
$A$, то по этой же причине диаграмма
$ #picard-quotient-triangle() $
удовлетворяет предположениям теоремы @th:exact-k-functor-triangle-sequence и
предложения @prop:exact-k-triangle-middle-criterion. Обозначим нулевую
относительную группу гомоморфизма $f: A -> B$ через $Pic(f)$ или через
$Pic(A, frak(q))$, если $f$ — факторгомоморфизм по идеалу $frak(q)$. Если
$F = tensor_A B: PicCat(A) -> PicCat(B)$, то легко заметить, что относительная
группа, обозначаемая через $K_1 (PicCat(A), F)$, есть не что иное, как
$ U(A, frak(q)) = Ker(U(A) -> U(B)) = Ker(U(A) -> U(A slash frak(q))), $
где $frak(q) = Ker(f)$. В этих обозначениях мы сформулируем результаты из
гл.~@ch:exact-k-sequences, §~@sec:cofinal-functor-exact-sequence, которые
упоминались выше.

#theorem[
  Гомоморфизм колец $f: A -> B$ с ядром $frak(q)$ индуцирует точную
  последовательность #numbered-condition[
    $ 0 -> U(A, frak(q)) -> U(A) -> U(B) -> Pic(f) -> Pic(A) -> Pic(B). $
  ] <eq:relative-picard-exact-sequence>
  (Мы используем обозначение $Pic(A, frak(q))$ для группы $Pic(f)$, если
  отображение $f$ сюръективно.) Если $frak(q)'$ — идеал, содержащий $frak(q)$,
  то точна последовательность #numbered-condition[
    $
      0 -> U(A, frak(q)) -> U(A, frak(q)') ->
      U(A slash frak(q), frak(q)' slash frak(q)) -> Pic(A, frak(q)) ->
      Pic(A, frak(q)') -> Pic(A slash frak(q), frak(q)' slash frak(q)).
    $
  ] <eq:nested-ideal-picard-exact-sequence>
] <th:relative-picard-exact-sequences>

#proposition[
  Допустим, что $frak(q) subset rad A$. Тогда отображение
  $Pic(A) -> Pic(A slash frak(q))$ есть мономорфизм; оно является изоморфизмом,
  если кольцо $A$ $frak(q)$-адически полно. Кроме того, отображение
  $U(A) -> U(A slash frak(q))$ — эпиморфизм. Поэтому $Pic(A, frak(q)) = 0$.
] <prop:radical-ideal-picard-invariance>
#proof[
  Эти утверждения доказываются точно так же, как и их $K$-аналоги в предложении
  @prop:k-radical-ideal-comparison.
]

#proposition[
  Если кольцо $A$ полулокально, то для всех идеалов $frak(q)$ отображение
  $U(A) -> U(A slash frak(q))$ сюръективно и $Pic(A) = 0 = Pic(A, frak(q))$.
] <prop:semilocal-picard-trivial>
#proof[
  Равенство нулю группы $Pic(A)$ следует, например, из теоремы Серра
  @cor:serre-free-summand. Сюръективность отображения
  $U(A) -> U(A slash frak(q))$ вытекает из @prop:semilocal-unit-in-coset. Из
  рассмотрения точной последовательности @eq:relative-picard-exact-sequence
  получаем, что $Pic(A, frak(q)) = 0$.
]

Следующая наша цель — построить сохраняющий произведение функтор
$ det: bold(P)(A) -> PicCat(A). $#symbol-idx(
  $det$,
  sort: "det",
  group: "operators",
  order: 40,
)
#source(361)Если $[P: A] = r$, то $det(P) = Lambda^r P$ ($r$-я внешняя степень).
Однако нам надо сделать ряд замечаний, чтобы пояснить построение этого функтора
в том случае, когда функция $r$ не является постоянной на $spec(A)$.

Напомним, что _внешняя алгебра_ модуля $M in moduleCategory-A$ является
градуированной антикоммутативной алгеброй
$ Lambda M = Lambda^0 M plus.o Lambda^1 M plus.o Lambda^2 M plus.o dots $
над кольцом $A = Lambda^0 M$. Кроме того, вложение
$M = Lambda^1 M subset Lambda M$ является универсальным среди $A$-линейных
отображений $h: M -> Lambda'$, где $Lambda'$ есть $A$-алгебра и $h(x)^2 = 0$ для
всех $x in M$. Используя это свойство универсальности, легко установить
естественный изоморфизм
$ Lambda(M plus.o N) tilde.eq Lambda(M) tensor_A Lambda(N), $
где тензорное произведение в правой части рассматривается в смысле
градуированных алгебр. В частности, для каждого $r >= 0$ найдется естественный
изоморфизм $A$-модулей #numbered-condition[
  $
    Lambda^r (M plus.o N) tilde.eq
    union.sq.big_(0<=i<=r) Lambda^i (M) tensor_A Lambda^(r-i) (N).
  $
] <eq:exterior-power-direct-sum>
Кроме того, $Lambda^i (A) = 0$, если $i > 1$.

Итак, из @eq:exterior-power-direct-sum следует, что
$ Lambda^r (A^n) tilde.eq A^(c_(n,r)), $
где $c_(n,r)$ — (биномиальный) коэффициент при $t^r$ в $(1+t)^n$. В частности,
#numbered-condition[
  $
    Lambda^n (A^n) tilde.eq A quad "и" quad Lambda^r (A^n) = 0,
    "если" r > n.
  $
] <eq:top-exterior-power-free-module>
Допустим, что $1 = sum e_i$, где $e_i$ — ортогональные идемпотенты кольца $A$.
Тогда для каждого модуля $M in moduleCategory-A$ получаем каноническое
отождествление $M = union.sq.big M e_i$. В частности,
$Lambda^r M = union.sq.big Lambda^r (M) e_i$ для любого числа $r >= 0$. (Мы не
пишем $Lambda^r (M e_i)$, что отлично от $Lambda^r (M) e_i$ при $r = 0$.)

Предположим далее, что $r$ — любая непрерывная функция из $spec(A)$ в $ZZ$,
принимающая лишь неотрицательные значения. Тогда, как и выше, запишем
$1 = sum e_i$ так, чтобы функция $r$ была постоянна, например, ее значение было
равно $r_i$ на $supp(e_i A)$ для каждого $i$. Тогда положим
$ Lambda^r M = union.sq.big Lambda^(r_i) (M) e_i. $
Если заменить разложение $1 = sum e_i$ более тонким разложением, то изложенное в
предыдущем параграфе показывает, что новое полученное определение для
$Lambda^r M$ канонически отождествляется с данным выше. Так как любые два
разложения обладают общим #source(362)продолжением, то мы видим, что
$Lambda^r M$ определено корректно и является функтором (конечно, неаддитивным)
от $M$.

Если $f: A -> B$ — гомоморфизм колец, то существует естественный изоморфизм
$Lambda_A (M) tensor_A B tilde.eq Lambda_B (M tensor_A B)$, т. е. функтор
$Lambda$ перестановочен с заменой колец. Отсюда следует, что существует
естественный изоморфизм
$Lambda_A^r (M) tensor_A B tilde.eq Lambda_B^(r') (M tensor_A B)$, где
$r' in H_0 (B)$ является образом элемента $r in H_0 (A)$. В частности, имеет
место следующая согласованность с локализацией: #numbered-condition[
  $
    Lambda^r (M)_(frak(p)) tilde.eq Lambda^(r(frak(p))) (M_(frak(p)))
    quad (frak(p) in spec(A)).
  $
] <eq:exterior-power-localization>
Наконец, мы хотим определить
$ det: bold(P)(A) -> PicCat(A), quad det(P) = Lambda^([P:A]) (P). $
Локализуя и используя @eq:exterior-power-localization и
@eq:top-exterior-power-free-module, убеждаемся в том, что $det(P) in PicCat(A)$.
Если $[P: A] = r$ и $[Q: A] = s$ — константы, то
$Lambda^i (P) = 0 = Lambda^j (Q)$ для $i > r$ и $j > s$. Следовательно,
изоморфизм @eq:exterior-power-direct-sum для $Lambda^(r+s)$ в этом случае
превращается в отображение
#numbered-condition[$ det(P plus.o Q) tilde.eq det(P) tensor_A det(Q). $]
<eq:determinant-direct-sum>
На самом деле такой естественный изоморфизм существует и в общем случае. В силу
способа определения функтора $det$ можно выбрать разложение $1 = sum e_i$ таким
образом, чтобы $[P: A]$ и $[Q: A]$ являлись константами на $supp(e_i A)$ для
каждого $i$. Затем легко свести построение изоморфизма
@eq:determinant-direct-sum к случаю модулей постоянного ранга.

Если ограничить морфизмы в категории $bold(P)(A)$ до изоморфизмов (это не
затрагивает группы $K_i (A) = K_i (bold(P)(A))$ и связанной с этими функторами
точной последовательности), то $det$ является функтором. Кроме того, он
естествен в том смысле, что если $f: A -> B$ — гомоморфизм колец, то диаграмма
$ #determinant-naturality() $
коммутативна с точностью до естественного изоморфизма. После некоторой
локализации это сводится к случаю модулей постоянного ранга, где это уже следует
из перестановочности функтора $Lambda$ с заменой колец. Из этих соображений
получаем морфизм точных последовательностей:
#numbered-condition[$ #determinant-exact-sequences() $]
<eq:determinant-exact-sequence-morphism>

#source(363)Если $P in PicCat(A)$, то $det(P) = Lambda^1 P = P$. Если же
$u in Aut_A (P)$, то $det_1 (u) = u$. Кроме того, если
$[P, alpha, Q]_(bold(P)) in K'_0 (f)$, где $P, Q in PicCat(A)$, то
$det_0 (f)[P, alpha, Q]_(bold(P)) = [P, alpha, Q]_(PicCat)$. Отсюда вытекает,
что вертикальные отображения в диаграмме @eq:determinant-exact-sequence-morphism
являются эпиморфизмами. (Вложение $PicCat subset bold(P)$ не сохраняет
произведения и поэтому не индуцирует гомоморфизм.)

Напомним, что $K_0 (A) tilde.eq H_0 (A) plus.o Rk_0 (A)$, где первый член
порождается всеми элементами вида $[e A]$, причем $e^2 = e$. Так как число
$[e A: A]$ равно нулю на $supp((1-e)A)$ и единице на $supp(e A)$, то
$
  det(e A) = (1-e)(Lambda^0 e A) plus.o e(Lambda^1 e A)
  = (1-e)A plus.o e(e A) = A.
$
Следовательно, $det_0 (A)$ — тривиальная функция на первом члене $H_0 (A)$, и
остается эпиморфизм
$ det_0 (A): Rk_0 (A) -> Pic(A). $
Если $Im(K'_0 (f) -> K_0 (A)) subset Rk_0 (A)$, т. е. если отображение
$H_0 (A) -> H_0 (B)$ является мономорфизмом, то в диаграмме
@eq:determinant-exact-sequence-morphism можно заменить группы $K_0$ на группы
$Rk_0$, сохраняя ее точность. В силу @lem:rank-function-base-change это имеет
место в том случае, когда $Ker(f)$ не содержит ненулевых идемпотентов.

#proposition[
  Если $f: A -> B$ — гомоморфизм колец, ядро которого не содержит ненулевых
  идемпотентов, то существует эпиморфизм точных последовательностей:
  $ #determinant-exact-sequences(reduced: true) $
] <prop:reduced-determinant-exact-sequence>

Приведем интерпретацию следующего свойства: $det_0$ является изоморфизмом.
Напомним, что $A$-модули $M$ и $N$ называются _стабильно изоморфными_#idx(
  "стабильно изоморфные модули",
), если $M plus.o A^n tilde.eq N plus.o A^n$ для некоторого $n >= 0$.

#proposition[
  Следующие условия эквивалентны:
  #condition-list[
    #condition-item(format: "cyrillic")[$det_0 (A): Rk_0 (A) -> Pic(A)$
      является изоморфизмом;] <cond:reduced-determinant-isomorphism>
    #condition-item(format: "cyrillic")[если ранг модуля $P in bold(P)(A)$
      постоянен и равен $r > 0$, то модуль $P$ стабильно изоморфен модулю
      $det P plus.o A^(r-1)$;] <cond:stable-determinant-free-decomposition>
    #condition-item(format: "cyrillic")[
      #condition-list[
        #condition-item[проективный модуль постоянного ранга стабильно изоморфен
          прямой сумме обратимых модулей;]
        <cond:stable-invertible-module-decomposition>
        #condition-item[если $P, Q in PicCat(A)$, то модуль $P plus.o Q$
          стабильно изоморфен модулю $(P tensor_A Q) plus.o A$.]
        <cond:stable-invertible-tensor-sum>
      ]
    ] <cond:stable-invertible-decomposition-and-tensor-sum>
  ]
] <prop:reduced-determinant-stable-characterization>
#proof[
  #source(364)$#[@cond:reduced-determinant-isomorphism] =>
  #[@cond:stable-determinant-free-decomposition]$. Заметим, что определитель
  элемента
  $ ([P] - [A^r]) - ([det P] - [A]) in Rk_0 (A) $
  тривиален. Поэтому из @cond:reduced-determinant-isomorphism следует, что
  $[P plus.o A] = [det P plus.o A^r]$. Из этого в свою очередь вытекает
  @cond:stable-determinant-free-decomposition.

  $#[@cond:stable-determinant-free-decomposition] =>
  #[@cond:stable-invertible-decomposition-and-tensor-sum]$. Утверждение
  @cond:stable-invertible-module-decomposition очевидно. Утверждение
  @cond:stable-invertible-tensor-sum доказывается сразу же, как только мы
  заметим, что $det(P plus.o Q) = P tensor_A Q$.

  $#[@cond:stable-invertible-decomposition-and-tensor-sum] =>
  #[@cond:reduced-determinant-isomorphism]$. Из условия
  @cond:stable-invertible-tensor-sum следует, что отображение
  $[P]_(Pic) arrow.r.bar [P]_(bold(P)) - [A]_(bold(P))$ определяет гомоморфизм
  $h: Pic(A) -> Rk_0 (A)$, при этом $det_0 (A) compose h = 1_(Pic(A))$. Из
  условия @cond:stable-invertible-module-decomposition следует, что отображение
  $h$ сюръективно. Это показывает, что $det_0 (A)$ является изоморфизмом.
]

#corollary[
  Если $maxSpec(A)$ — нётерово пространство размерности $<= 1$, то отображение
  $det_0 (A): Rk_0 (A) -> Pic(A)$ — изоморфизм.
] <cor:dimension-one-reduced-determinant-isomorphism>
#proof[
  Из теоремы Серра @cor:serre-free-summand следует, что модуль $P$,
  удовлетворяющий приведенному выше условию
  @cond:stable-determinant-free-decomposition, изоморфен модулю вида
  $L plus.o A^(r-1)$ для некоторого модуля $L$, ранг которого обязательно
  равен 1. Таким образом,
  $
    det P = det(L plus.o A^(r-1)) tilde.eq det L tensor det(A^(r-1))
    tilde.eq L tensor_A A = L,
  $
  что завершает доказательство предложения.
]

Закончим этот параграф рядом замечаний о функторе $det_1$. В силу определения
обычного определителя, с учетом изоморфизма $K_1 (A) tilde.eq GL(A) slash E(A)$,
отображение $det_1 (A)$ индуцируется отображением $det: GL(A) -> U(A)$.
Отображение $U(A) = GL_1 (A) -> GL(A)$ расщепляет этот определитель. Поэтому мы
получаем канонически расщепляемую короткую точную последовательность
$ 0 -> SK_1 (A) -> K_1 (A) arrow.r^(det_1 (A)) U(A) -> 0, $
где $SK_1 (A) = SL(A) slash E(A)$. Аналогично для любого идеала
$frak(q) subset A$ мы получаем каноническое разложение
$ K_1 (A, frak(q)) = U(A, frak(q)) plus.o SK_1 (A, frak(q)). $
Таким образом, из теоремы @th:ideal-relative-k-exact-sequences вытекает

#proposition[
  Если $frak(q) subset frak(q)'$ — идеалы кольца $A$, то существуют точные
  последовательности
  $ SK_1 (A, frak(q)) -> SK_1 (A) -> SK_1 (A slash frak(q)) $
  и
  $
    SK_1 (A, frak(q)) -> SK_1 (A, frak(q)') ->
    SK_1 (A slash frak(q), frak(q)' slash frak(q)).
  $
] <prop:relative-sk-one-exact-sequences>

#source(365)
#proposition[
  Пусть $frak(q)$ — идеал кольца $A$ и $frak(a) = ann_A (frak(q))$. Если либо
  $frak(q) subset rad A$, либо кольцо $A slash frak(a)$ полулокально, то
  $SK_1 (A, frak(q)) = 0$.
] <prop:annihilator-semilocal-sk-one-vanishing>
#proof[
  Из @prop:k-radical-ideal-comparison, @cond:k-one-radical-quotient-surjection
  следует, что группа $SK_1 (A, frak(q))$ равна нулю, если
  $frak(q) subset rad A$. Равенство нулю в случае полулокального кольца следует
  из @prop:semilocal-k-groups.

  Пусть $frak(q)_0 = frak(q) inter frak(a)$. Так как $frak(q) dot frak(a) = 0$,
  то $frak(q)_0^2 = 0$, и, следовательно, $frak(q)_0 subset rad A$. В силу
  точности последовательности
  $
    0 -> SK_1 (A, frak(q)_0) -> SK_1 (A, frak(q)) ->
    SK_1 (A slash frak(q)_0, frak(q) slash frak(q)_0)
  $
  мы видим, что достаточно доказать равенство $SK_1 (A', frak(q)') = 0$, где
  $A' = A slash frak(q)_0$, $frak(q)' = frak(q) slash frak(q)_0$. Если положить
  $frak(a)' = frak(a) slash frak(q)_0$, то $frak(q)' inter frak(a)' = 0$. Таким
  образом, из @prop:disjoint-ideal-relative-k-decomposition следует, что
  отображение
  $
    SK_1 (A', frak(q)') ->
    SK_1 (A' slash frak(a)', (frak(q)' + frak(a)') slash frak(a)')
  $
  является мономорфизмом (даже изоморфизмом). Так как кольцо
  $A' slash frak(a)' = A slash frak(a)$ полулокально, то последняя группа равна
  нулю. Тем самым предложение доказано.
]

#corollary[
  Пусть $frak(q) subset frak(q)'$ — идеалы и
  $frak(a) = ann_A (frak(q)' slash frak(q))$. Если кольцо $A slash frak(a)$
  полулокально, то отображение $SK_1 (A, frak(q)) -> SK_1 (A, frak(q)')$
  является эпиморфизмом.
] <cor:annihilator-semilocal-sk-one-surjection>
#proof[
  Применим предложение @prop:annihilator-semilocal-sk-one-vanishing. Тогда
  группа $SK_1 (A slash frak(q), frak(q)' slash frak(q))$ в точной
  последовательности @prop:relative-sk-one-exact-sequences равна нулю.
]
