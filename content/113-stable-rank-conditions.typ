#import "diagrams/stable-linear-groups-stable-rank.typ": diagram-stable-rank
#import "main-defs.typ": (
  E, GE, GL, Ker, SL, SR, U, idx, name-idx, rad, source, symbol-idx, transpose,
)
#import "statements.typ": (
  condition-item, condition-list, definition, proof, proposition, theorem,
  variant-definition,
)

== Условия стабильности ранга $SR_n (A, frak(q))$ <sec:stable-rank-conditions>

Основные теоремы этой главы формулируются в следующем параграфе. В их
формулировки входят некоторые технические предположения, которые мы приведем и
рассмотрим в этом параграфе. В частности, используя теоремы, доказанные в
гл.~@ch:stable-projective-structure, мы покажем, что эти предположения
выполняются в достаточно широком классе колец.

_В следующих далее трех определениях будут фиксированы кольцо $A$ и двусторонний
идеал $frak(q)$ кольца $A$._ Напомним, что элемент
$alpha = (a_1, dots, a_n) in A^n$ называется унимодулярным в $A^n$, если
существует гомоморфизм $f: A^n -> A$, такой, что $f(alpha) = 1$. Это, очевидно,
эквивалентно тому, что $sum A a_i = A$. Если, кроме того,
$alpha equiv (1, 0, dots) mod frak(q)$, то будем говорить, что элемент $alpha$
$frak(q)$-унимодулярен.

#definition[
  Условие#footnote[«Стабильности ранга». — _Прим. ред._]
  $SR_n (A, frak(q))$:#idx("условия стабильности ранга")

  Если $m >= n$ и если $alpha = (a_1, dots, a_m) in A^m$ есть
  $frak(q)$-унимодулярный элемент, то существуют элементы
  $a'_i = a_i + b_i a_m$, где $b_i in frak(q)$ #source(191)$(1 <= i < m)$,
  такие, что элемент $(a'_1, dots, a'_(m - 1)) in A^(m - 1)$
  унимодулярен.#footnote[
    Достаточно потребовать выполнения условия при $m = n$ (тогда оно будет
    выполнено и при $m > n$). См. Васерштейн @bib:Vaserstein1969a.#name-idx(
      "Васерштейн Л. Н.",
    ) — _Прим. ред._
  ]
]
<def:relative-stable-rank>

Если $frak(q) = A$, то вместо $SR_n (A, A)$ будем использовать обозначение
$SR_n (A)$. Заметим, что условие $SR_n (A, frak(q))$ может выполняться лишь при
$n >= 2$.

Очевидно, что
$
  SR_n (A, frak(q)) => SR_m (A, frak(q)) quad "для всех" m >= n.
$
Условие, аналогичное условию $SR_n (A, frak(q))$, для правого (вместо левого)
идеала, порожденного элементами строки $alpha in A^n$, можно записать как
$SR_n (A^o, frak(q))$, где $A^o$ — противоположное кольцо для кольца $A$.

#variant-definition[
  Условие $SR'_n (A, frak(q))$:

  Группа $GL_n (A, frak(q))$ действует транзитивно на $frak(q)$-унимодулярных
  элементах модуля $A^n$.
] <def:relative-unimodular-transitivity>

Как и раньше при $frak(q) = A$, это условие обозначим через $SR'_n (A)$.
Заметим, что в этом определении налагается условие лишь на $A^n$, а не на все
$A^m$ $(m >= n)$, как это было в определении @def:relative-stable-rank.

Прежде чем сформулировать последнее условие, мы должны ввести некоторые новые
обозначения и термины. Через $overline(E)_m (A, frak(q))$#symbol-idx(
  $overline(E)_m (A, frak(q))$,
  sort: "overline E_m(A,q)",
  group: "groups",
  order: 89,
) обозначим группу, порожденную группами $E_m (A, frak(q))$ и
$[GE_m (A), GL_m (A, frak(q))]$. Из @cor:relative-elementary-commutators
следует, что
$
  overline(E)_m (A, frak(q)) = [GE_m (A), GL_m (A, frak(q))]
  quad "для всех" m >= 3.
$ <eq:extended-elementary-commutators>

Пусть $t in A$. Будем говорить, что $alpha in GL_m (A)$ — элемент типа
$(frak(q), t)$, если матрица $alpha$ имеет вид
$
  alpha = mat(1 + a t, alpha_12; alpha_21 t, alpha_22),
$
где $a in frak(q)$, $alpha_22 in M_(m - 1) (A)$, и элементы матриц $alpha_12$ и
$#transpose($alpha_21$, mark: $T$)$ лежат в $frak(q)$. Для такой матрицы
определим
$
  alpha' = mat(1 + t a, t alpha_12; alpha_21, alpha_22)
$
и будем говорить, что матрица $alpha'$, полученная таким образом,
$(frak(q), t)$-связана с матрицей $alpha$.#idx("(q,t)-связанные матрицы") К
сожалению, так как элемент $t$ может быть делителем нуля, то матрица $alpha$ не
определяет матрицу $alpha'$.

#variant-definition[
  Условие $SR''_n (A, frak(q))$:

  Если $t in frak(q)$, если $alpha in GL_n (A, frak(q))$ — матрица типа
  $(frak(q), t)$ и если матрица $alpha'$ $(frak(q), t)$-связана с $alpha$, то
  $alpha' alpha^(-1) in overline(E)_n (A, frak(q))$.
] <def:relative-linked-matrix-stability>

#source(192)Это условие выглядит, возможно, довольно искусственным, однако оно
неизбежно возникает из материала
§~@sec:linear-stability-homomorphism-construction.

#proposition[
  Пусть $f: A -> A'$ — сюръективный гомоморфизм колец. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[Если $frak(q)_0 subset frak(q)$ — два
      двусторонних идеала кольца $A$, то
      $SR_n (A, frak(q)) => SR_n (A, frak(q)_0)$. В частности,
      $SR_n (A) => SR_n (A, frak(q))$ для всех $frak(q)$.]
    <cond:stable-rank-ideal-restriction>

    #condition-item(format: "cyrillic")[Если $frak(q)'$ — двусторонний идеал
      кольца $A'$, то $SR_n (A, f^(-1) (frak(q)')) => SR_n (A', frak(q)')$. В
      частности, $SR_n (A) => SR_n (A')$.]
    <cond:stable-rank-quotient>
  ]
] <prop:stable-rank-ideals-quotients>

#proof[
  #condition-list[
    #condition-item(format: "cyrillic")[Предположим, что $m >= n$ и
      $alpha = (a_1, dots, a_m)$ есть $frak(q)_0$-унимодулярный элемент.
      Записывая $1 = sum_i c_i a_i$ $(c_i in A)$, получаем, что
      $a_m = sum_i a_m c_i a_i$, и поэтому элемент $a_m$ лежит в левом идеале,
      порожденном координатами строки
      $alpha' = (a_1, dots, a_(m - 1), a_m c_m a_m)$. Отсюда следует, что
      $alpha'$ — унимодулярный элемент и, следовательно, $frak(q)$-унимодулярен.
      В силу предположения найдутся такие элементы
      $a'_i = a_i + b_i a_m c_m a_m$, где $b_i in frak(q)$ $(1 <= i < m)$, что
      строка $(a'_1, dots, a'_(m - 1))$ унимодулярна. Так как
      $b_i a_m c_m in frak(q)_0$ (ибо $a_m in frak(q)_0$), то справедливо
      $SR_n (A, frak(q)_0)$.#footnote[
        @prop:stable-rank-ideals-quotients @cond:stable-rank-ideal-restriction
        не обобщается на случай левых идеалов $frak(q)_0$, см. Васерштейн
        @bib:Vaserstein1971. — _Прим. ред._
      ]] <cond:stable-rank-ideal-restriction-proof>

    #condition-item(format: "cyrillic")[Предположим, что $m >= n$. Покажем
      сначала, что $frak(q)'$-унимодулярный элемент
      $alpha' = (a'_1, dots, a'_m) in A'^m$ можно поднять до унимодулярного
      элемента $alpha = (a_1, dots, a_m) in A^m$ (т.~е. $f(alpha) = alpha'$).
      Действительно, пусть $alpha$ — произвольный прообраз элемента $alpha'$.
      Запишем $1 = sum_i f(c_i) a'_i$, где $c_i in A$ $(1 <= i <= m)$. Тогда
      $1 = sum_i c_i a_i + q$ для некоторого элемента
      $q in Ker(f) subset f^(-1) (frak(q)')$. Следовательно,
      $(a_1, dots, a_m, q)$ есть $f^(-1) (frak(q)')$-унимодулярный элемент в
      $A^(m + 1)$, поэтому существуют элементы $b_i = a_i + t_i q$
      $(1 <= i <= m)$, такие, что элемент $beta = (b_1, dots, b_m)$ унимодулярен
      (по предположению). Очевидно, $f(beta) = alpha'$, потому $beta$
      $f^(-1) (frak(q)')$-унимодулярен.

      Опять же в силу предположения можно найти элементы $d_i = b_i + s_i b_m$,
      где $f(s_i) in frak(q)'$ $(1 <= i < m)$, такие, что элемент
      $delta = (d_1, dots, d_(m - 1))$ унимодулярен. Но теперь элементы
      $f(d_i) = a'_i + f(s_i) a'_m$ решают нашу
      задачу.] <cond:stable-rank-quotient-proof>
  ]
]

#theorem[
  Пусть выполнено $SR_n (A, frak(q))$, и пусть $m >= n$.
  #condition-list[
    #condition-item[Группа $E_m (A, frak(q))$ действует транзитивно на
      $frak(q)$-унимодулярных элементах модуля $A^m$. В частности,
      $SR_n (A, frak(q)) => SR'_m (A, frak(q))$. Кроме того, $E_m (A, frak(q))$
      — нормальный делитель группы $GL_m (A, frak(q))$, и
      $GL_m (A, frak(q)) = E_m (A, frak(q)) dot GL_(n - 1) (A, frak(q))$.]
    <cond:stable-rank-elementary-transitivity>

    #condition-item[Пусть $t in A$ и $alpha in GL_m (A, frak(q))$ — матрица типа
      $(frak(q), t)$. Если матрица $alpha'$ $(frak(q), t)$-связана с матрицей
      $alpha$, то $alpha' in GL_m (A, frak(q))$ и
      $alpha' alpha^(-1) in E_m (A, frak(q))$. В частности,
      $SR_n (A, frak(q)) => SR''_m (A, frak(q))$.]
    <cond:stable-rank-linked-matrix-equivalence>
  ]
] <th:stable-rank-relative-elementary-stability>

#source(193)#proof[
  Мы могли бы вывести утверждение @cond:stable-rank-elementary-transitivity из
  @th:elementary-unimodular-transitivity, но детали рассуждений понадобятся для
  второй части теоремы. Проведем доказательство в несколько шагов.

  #condition-list[
    #condition-item(format: "(i)")[_Пусть $alpha, beta in GL_m (A)$ — элементы
      типа $(frak(q), t)$, и пусть $alpha'$ и $beta'$ $(frak(q), t)$-связаны с
      $alpha$ и $beta$ соответственно. Тогда $alpha beta$ — элемент типа
      $(frak(q), t)$ и элемент $alpha' beta'$ $(frak(q), t)$-связан с
      $alpha beta$._

      Пусть $alpha'$ и $beta'$ определены по представлениям матриц $alpha$ и
      $beta$ в виде
      $
        alpha = mat(1 + a t, alpha_12; alpha_21 t, alpha_22), quad
        beta = mat(1 + b t, beta_12; beta_21 t, beta_22).
      $
      Тогда
      $
        alpha beta = mat(
          1 + (a + b + a t b + alpha_12 beta_21) t,
          beta_12 + a t beta_12 + alpha_12 beta_22;
          (alpha_21 + alpha_21 t b + alpha_22 beta_21) t,
          alpha_21 t beta_12 + alpha_22 beta_22
        )
      $
      и
      $
        alpha' beta' = mat(
          1 + t(a + b + a t b + alpha_12 beta_21),
          t(beta_12 + a t beta_12 + alpha_12 beta_22);
          alpha_21 + alpha_21 t b + alpha_22 beta_21,
          alpha_21 t beta_12 + alpha_22 beta_22
        ).
      $
    ] <cond:linked-matrix-product>

    #condition-item(format: "(i)")[_Предположим, что $#transpose(
        $gamma$,
        mark: $T$,
      ) = (a_1, dots, a_m)
      equiv (1, 0, dots, 0) mod frak(q) t$ и элемент $gamma$ унимодулярен. Тогда
      найдется элемент $tau in E_m (A, frak(q))$ типа $(frak(q), t)$, такой, что
      $tau gamma = #transpose($(1, 0, dots, 0)$, mark: $T$)$ и такой, что
      существует элемент $tau' in E_m (A, frak(q))$, который
      $(frak(q), t)$-связан с $tau$._

      Сначала применим определение @def:relative-stable-rank для того, чтобы
      найти элементы $a'_i = a_i + b_i a_m$, где $b_i in frak(q)$
      $(1 <= i < m)$, такие, что строка $(a'_1, dots, a'_(m - 1))$ унимодулярна.
      Положим $tau_1 = I + sum_(1 <= i < m) b_i e_(i m)$. Так как первый столбец
      матрицы $tau_1$ тривиален, то она типа $(frak(q), t)$, и мы можем
      определить матрицу $tau'_1 in E_m (A, frak(q))$ (например,
      $tau'_1 = I + t b_1 e_(1 m) + sum_(1 < i < m) b_i e_(i m)$),
      $(frak(q), t)$-связанную с матрицей $tau_1$. Кроме того,
      $tau_1 gamma = #transpose($(a'_1, dots, a'_(m - 1), a_m)$, mark: $T$)
      equiv #transpose($(1, 0, dots, 0)$, mark: $T$) mod frak(q) t$. Запишем
      $1 = sum_(i < m) c_i a'_i$ и положим
      $tau_2 = I + (sum_(i < m) (1 - a'_1 - a_m) c_i e_(m i))$. Так как
      $1 - a'_1 - a_m in frak(q) t$ и $c_1 equiv 1 mod frak(q) t$, то мы видим,
      что $tau_2$ — матрица типа $(frak(q), t)$. Опять можно определить матрицу
      $tau'_2 in E_m (A, frak(q))$, $(frak(q), t)$-связанную с матрицей $tau_2$.
      Кроме того, $tau_2 tau_1 gamma = #transpose(
        $(a'_1, dots, a'_(m - 1), 1 - a'_1)$,
        mark: $T$,
      )$. Но у матрицы $epsilon = I + e_(1 m) in E_m (A)$ первый столбец
      тривиален; положим $epsilon' = I + t e_(1 m) in E_m (A)$. Кроме того,
      $epsilon tau_2 tau_1 gamma = #transpose(
        $(1, a'_2, dots, a'_(m - 1), 1 - a'_1)$,
        mark: $T$,
      )$. Положим
      $tau_3 = I - (sum_(1 < i < m) a'_i e_(i 1)) - (1 - a'_1) e_(m 1)
      in E_m (A, frak(q))$. Как и ранее, можно определить матрицу
      $tau'_3 in E_m (A, frak(q))$, $(frak(q), t)$-связанную с $tau_3$. Кроме
      того,
      $tau_3 epsilon tau_2 tau_1 gamma = #transpose(
        $(1, 0, dots, 0)$,
        mark: $T$,
      )$
      и последняя матрица остается неподвижной при действии $epsilon$. Таким
      образом, $tau = tau_3^epsilon tau_2 tau_1 in E_m (A, frak(q))$ и
      $tau gamma = #transpose($(1, 0, dots, 0)$, mark: $T$)$. #source(194)Прямое
      умножение показывает, что $tau_3^epsilon$ — матрица типа $(frak(q), t)$,
      связанная с $(tau'_3)^(epsilon')$. Поэтому из @cond:linked-matrix-product
      следует, что $tau$ — матрица типа $(frak(q), t)$ и что матрица
      $tau' = (tau'_3)^(epsilon') tau'_2 tau'_1$ $(frak(q), t)$-связана с $tau$.
      Очевидно также, что $tau' in E_m (A, frak(q))$.]
    <cond:linked-unimodular-reduction>

    #condition-item(format: "(i)")[#emph[Доказательство
        п.~@cond:stable-rank-elementary-transitivity.]

      Если $t = 1$, то $frak(q) t = frak(q)$ и из
      @cond:linked-unimodular-reduction следует, что группа $E_m (A, frak(q))$
      действует транзитивно на $frak(q)$-унимодулярных элементах модуля $A^m$.
      Если $sigma in GL_m (A, frak(q))$, то, следовательно, можно найти матрицу
      $tau_1 in E_m (A, frak(q))$, такую, что последний столбец матрицы
      $tau_1 sigma$ совпадает с $#transpose($(0, dots, 0, 1)$, mark: $T$)$.
      Пусть
      $
        tau_1 sigma = mat(alpha, 0; rho, 1)
        = mat(I, 0; rho alpha^(-1), 1) mat(alpha, 0; 0, 1).
      $
      Левый множитель, очевидно, лежит в $E_m (A, frak(q))$, и
      $alpha in GL_(m - 1) (A, frak(q))$. Таким образом,
      $GL_m (A, frak(q)) = E_m (A, frak(q)) GL_(m - 1) (A, frak(q))$. Проводя
      индукцию по $m - n$ $(>= 0)$, можно заключить, что
      $GL_m (A, frak(q)) = E_m (A, frak(q)) GL_(n - 1) (A, frak(q))$.

      Наконец, чтобы показать, что $E_m (A, frak(q))$ — нормальный делитель
      группы $GL_m (A, frak(q))$, возьмем один из образующих $tau^epsilon$
      группы $E_m (A, frak(q))$ (здесь матрица $tau$ $frak(q)$-элементарна и
      $epsilon in E_m (A)$). Так как группа $E_m (A)$ содержит все матрицы
      перестановки с определителем единица, то, меняя $epsilon$, можно считать,
      что $tau$ — матрица вида $tau = mat(I, 0; t, 1)$. Если
      $alpha in GL_m (A, frak(q))$, то
      $(tau^epsilon)^alpha = (tau^(epsilon alpha epsilon^(-1)))^epsilon$ и
      матрица $epsilon$ нормализует группу $E_m (A, frak(q))$. Следовательно,
      заменяя $alpha$ на $epsilon alpha epsilon^(-1)$, достаточно показать, что
      $tau^alpha in E_m (A, frak(q))$. Запишем
      $alpha^(-1) = epsilon_1^(-1) alpha_1^(-1)$, где
      $epsilon_1 in E_m (A, frak(q))$ и $alpha_1 in GL_(m - 1) (A, frak(q))$
      (используя первую часть доказательства). Тогда
      $tau^alpha = (tau^(alpha_1))^(epsilon_1)$, поэтому достаточно доказать,
      что $tau^(alpha_1) in E_m (A, frak(q))$. Но
      $
        mat(I, 0; t, 1)^(mat(alpha_1, 0; 0, 1))
        = mat(I, 0; t alpha_1, 1) in E_m (A, frak(q)),
      $
      что и требовалось.]
    <cond:stable-rank-transitivity-proof>

    #condition-item(format: "(i)")[#emph[Доказательство
        п.~@cond:stable-rank-linked-matrix-equivalence.]

      Пусть матрицы $alpha$ и $alpha'$ такие же, как и в части
      @cond:stable-rank-linked-matrix-equivalence. Применим
      @cond:linked-unimodular-reduction к первому столбцу $gamma_0$ матрицы
      $alpha$. Тогда получим матрицу $tau in E_m (A, frak(q))$ типа
      $(frak(q), t)$ и матрицу $tau' in E_m (A, frak(q))$,
      $(frak(q), t)$-связанную с $tau$, такие, что матрица $delta = tau alpha$
      имеет вид $delta = mat(1, rho; 0, beta)$. Тогда матрица
      $delta' = mat(1, t rho; 0, beta)$ $(frak(q), t)$-связана с $delta$, и
      очевидно, что $delta' delta^(-1) in E_m (A, frak(q))$. Положим
      $delta_0 = tau' alpha'$. Тогда из @cond:linked-matrix-product следует, что
      матрица $delta_0$ является $(frak(q), t)$-связанной с $tau alpha = delta$.
      Чтобы показать, что $alpha' alpha^(-1) in E_m (A, frak(q))$ (и таким
      образом, доказать @cond:stable-rank-linked-matrix-equivalence), достаточно
      #source(195)показать, что
      $delta_0 delta^(-1) = tau' alpha' alpha^(-1) tau^(-1)
      in E_m (A, frak(q))$. Далее, так как
      $delta_0 delta^(-1) = delta_0 (delta')^(-1) delta' delta^(-1)$, то
      достаточно показать, что $delta_0 (delta')^(-1) in E_m (A, frak(q))$. Но
      матрицы $delta_0$ и $delta'$ обе $(frak(q), t)$-связаны с одной и той же
      матрицей $delta = tau alpha = mat(1, rho; 0, beta)$. Из этого следует, что
      матрица $delta_0$ должна иметь вид
      $delta_0 = mat(1 + t a, t rho; gamma, beta)$, где $a t = 0$ и
      $gamma t = 0$. Таким образом,
      $
        delta_0 (delta')^(-1)
        = mat(1 + t a, t rho; gamma, beta)
        mat(1, -t rho beta^(-1); 0, beta^(-1))
        = mat(1 + t a, 0; gamma, I)
        = mat(1, 0; gamma, I) mat(1 + t a, 0; 0, I).
      $
      Левый множитель, очевидно, лежит в $E_m (A, frak(q))$. Для правого
      множителя справедливо следующее разложение в $GL_2 (A)$ (благодаря тому,
      что $a t = 0$):
      $
        mat(1 + t a, 0; 0, 1)
        = [mat(1, 0; a, 1), mat(1, -t; 0, 1)] in E_2 (A, frak(q)),
      $
      что и требовалось доказать.]
    <cond:stable-rank-linked-matrix-proof>
  ]
]

Соберем вместе в одну диаграмму установленные логические связи между условиями
стабильности ранга. Здесь $A$ — кольцо, $frak(q)_0 subset frak(q)$ — два
двусторонних идеала.

#diagram-stable-rank()

Наконец, приведем два результата, показывающие, что введенные условия
выполняются в довольно общей ситуации.

#proposition[
  Пусть $A$ — кольцо, $frak(q)$ — двусторонний идеал кольца $A$.
  #condition-list[
    #condition-item(format: "cyrillic")[Если $A$ — полулокальное кольцо или если
      $frak(q) subset rad A$, то выполнено условие
      $SR_2 (A, frak(q))$.] <cond:semilocal-relative-stable-rank>

    #source(196)#condition-item(format: "cyrillic")[Условие $SR'_1 (A, frak(q))$
      выполняется всегда. Если кольцо $A$ коммутативно, то справедливо условие
      $SR'_2 (A, frak(q))$.]
    <cond:commutative-rank-two-transitivity>
  ]
] <prop:semilocal-commutative-stable-rank>

#proof[
  #condition-list[
    #condition-item(format: "cyrillic")[Пусть элемент $(a_1, dots, a_m) in A^m$
      является $frak(q)$-унимодулярным $(m >= 2)$. Если $frak(q) subset rad A$,
      то $a_1 in U(A)$, так как $a_1 equiv 1 mod frak(q)$, поэтому элемент
      $(a_1, dots, a_(m - 1))$ унимодулярен. Если $A$ — полулокальное кольцо,
      то, поскольку $sum_i A a_i = A$, из @prop:semilocal-unit-in-coset следует,
      что $a_1 + sum_(i >= 2) b_i a_i in U(A)$ для некоторых
      $b_2, dots, b_m in A$. Таким образом, элемент
      $(a_1 + b_m a_m, a_2, dots, a_(m - 1))$ унимодулярен, и это показывает
      справедливость условия $SR_2 (A)$. В силу
      @prop:stable-rank-ideals-quotients @cond:stable-rank-ideal-restriction из
      этого следует, что имеет место условие
      $SR_2 (A, frak(q))$.] <cond:semilocal-relative-stable-rank-proof>

    #condition-item(format: "cyrillic")[Справедливость условия
      $SR'_1 (A, frak(q))$ очевидна. Предположим теперь, что кольцо $A$
      коммутативно. Пусть $alpha = #transpose($(a, b)$, mark: $T$) in A^2$ —
      унимодулярный элемент. Запишем $1 = a x + b y$, где $x, y in A$, и положим
      $c = -b y^2 in frak(q)$ и $d = x + b x y$. Тогда
      $a d - b c = a(x + b x y) + b^2 y^2 = a x + b y(a x + b y) = 1$.
      Рассматривая это по модулю $frak(q)$, убеждаемся, что
      $d equiv 1 mod frak(q)$, поэтому матрица $sigma = mat(a, c; b, d)$
      принадлежит группе $SL_2 (A, frak(q))$. Кроме того,
      $sigma mat(1; 0) = mat(a; b) = alpha$, что доказывает
      п.~@cond:commutative-rank-two-transitivity.]
    <cond:commutative-rank-two-transitivity-proof>
  ]
]

#theorem[
  Пусть $R$ — коммутативное кольцо, такое, что $max(R)$ — нётерово пространство,
  являющееся объединением конечного числа подпространств размерности $<= d$.
  Пусть $A$ — конечномерная $R$-алгебра. Тогда кольцо $A$ удовлетворяет условию
  $SR_(d + 2) (A)$.
] <th:stable-rank-dimension-bound>

#proof[
  Пусть $e_1, dots, e_m$ — стандартный базис модуля $A^m$. Допустим, что
  $m >= d + 2$. Пусть $alpha = sum_i e_i a_i$ — унимодулярный элемент. В силу
  @th:unimodular-element-adjustment найдется гомоморфизм
  $f: e_m A -> A^(m - 1)$, такой, что $(a_1, dots, a_(m - 1)) + f(e_m a_m)$ —
  унимодулярный элемент. Тогда строка $f(e_m) = (b_1, dots, b_(m - 1))$
  удовлетворяет требованиям определения @def:relative-stable-rank, что и
  требовалось доказать.
]
