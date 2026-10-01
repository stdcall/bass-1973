#import "main-defs.typ": E, GL, SR, source, transpose
#import "statements.typ": condition-item, condition-list, lemma, proof

#heading(level: 2)[Доказательство теоремы @th:relative-k1-stability: III.
  Заключительная часть]
<sec:linear-stability-final-proof>

Допустим, что $n >= 2$ и $pi$ определена в предложении
@prop:linear-character-normalizer-criterion. Положим
$ S = {sigma in GL_(n + 1) (A, frak(q)) | chi' (sigma^pi) = chi' (sigma)}. $
В силу @prop:linear-character-normalizer-criterion нам осталось доказать, что
$S = GL_(n + 1) (A, frak(q))$.

#lemma[
  Пусть $sigma in GL_(n + 1) (A, frak(q))$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[
      Если $overline(beta)_1 in GL_(n + 1) (A, frak(q))$ — матрица типа R и если
      $overline(alpha)_1 in GL_(n + 1) (A, frak(q))$ — матрица вида
      $ overline(alpha)_1 = mat(alpha'_1, gamma'_1; 0, I_2) $
      (где $alpha'_1 in GL_(n - 1) (A, frak(q))$), то
      $sigma in S <=> overline(alpha)_1 sigma overline(beta)_1 in S$.
    ] <cond:linear-stability-type-l-r-reduction>
    #condition-item(format: "cyrillic")[
      #source(214)Можно выбрать $overline(alpha)_1$ и $overline(beta)_1$ (в
      приведенной выше форме) таким образом, что
      $overline(alpha)_1 sigma overline(beta)_1 = overline(alpha) epsilon$, где
      $epsilon = I + a e_(n + 1, 1)$ и где
      $overline(alpha) = mat(alpha, gamma; 0, 1)$ — матрица типа L; здесь
      $gamma = #transpose($(0, dots, 0, c)$, mark: $T$)$. Допуская
      справедливость условия $SR_n (A, frak(q))$, можно подобрать первый столбец
      $#transpose($(a_1, dots, a_n)$, mark: $T$)$ матрицы $alpha$ так, что
      строка $(a_1, dots, a_(n - 1))$ будет унимодулярной. Если, далее,
      допустить, что справедливо условие $SR'_(n - 1) (A, frak(q))$, то можно
      добиться того, чтобы $(a_1, dots, a_(n - 1)) = (1, 0, dots, 0)$.
    ] <cond:linear-stability-last-column-reduction>
  ]
] <lem:linear-stability-transposition-invariance>

#proof[
  @cond:linear-stability-type-l-r-reduction Для указанных матриц
  $overline(alpha)_1$ и $overline(beta)_1 = mat(1, rho_1; 0, beta_1)$ матрица
  $overline(alpha)_1^pi = mat(alpha'_1, gamma''_1; 0, I_2)$ все еще типа L, а
  матрица $overline(beta)_1^pi = mat(1, rho'_1; 0, beta_1^(pi_1))$ — типа R.
  Следовательно, в силу @prop:linear-standard-form-character
  @cond:linear-standard-form-equivariance
  $chi' ((overline(alpha)_1 sigma overline(beta)_1)^pi)
  = chi' (overline(alpha)_1^pi) chi' (sigma^pi) chi' (overline(beta)_1^pi)$, и
  ясно, что $chi' (overline(alpha)_1^pi) = chi' (overline(alpha)_1)$ и
  $chi' (overline(beta)_1^pi) = chi' (overline(beta)_1)$. Это доказывает
  @cond:linear-stability-type-l-r-reduction.

  @cond:linear-stability-last-column-reduction Если
  $sigma = overline(alpha) epsilon overline(beta)$ — стандартная форма, то
  положим сначала $overline(beta)_1 = overline(beta)^(-1)$. Остается показать,
  как изменить теперь $overline(alpha) = mat(alpha, gamma; 0, 1)$, умножая слева
  на матрицу $overline(alpha)_1$ указанного вида. Матрицы этого типа, очевидно,
  образуют группу, и поэтому у нас появляется свобода совершать
  последовательность таких умножений слева.

  Пусть $gamma = #transpose($(c_1, dots, c_n)$, mark: $T$)$. Тогда, умножая
  слева на матрицу $mat(I, -gamma'; 0, 1)$, где
  $gamma' = #transpose($(c_1, dots, c_(n - 1), 0)$, mark: $T$)$
  (это умножение допустимо), мы заменим $gamma$ на
  $#transpose($(0, dots, 0, c)$, mark: $T$)$, где $c = c_n$, и не изменим
  $alpha$. Таким образом, мы можем добиться требуемого вида строки $gamma$, и
  даже если этот вид будет нарушен при операциях, вызванных задачами
  преобразования матрицы $alpha$, его можно восстановить, не причиняя вреда
  достигнутому виду матрицы $alpha$.

  Пусть $beta = #transpose($(a_1, dots, a_n)$, mark: $T$)$ — первый столбец
  матрицы $alpha$. Допуская справедливость условия $SR_n (A, frak(q))$, можно
  найти матрицу $alpha_1 = mat(I_(n - 1), gamma_1; 0, 1)
  in E_n (A, frak(q))$, такую, что
  $alpha_1 beta = #transpose($(a'_1, dots, a'_(n - 1), a_n)$, mark: $T$)$, где
  строка $(a'_1, dots, a'_(n - 1))$ унимодулярна. Умножая слева на матрицу
  $overline(alpha)_1 = mat(alpha_1, 0; 0, 1)$ (это допустимо), можно считать,
  что строка $(a_1, dots, a_(n - 1))$ унимодулярна. Допуская справедливость
  условия $SR'_(n - 1) (A, frak(q))$, можно затем найти матрицу
  $alpha_2 in GL_(n - 1) (A, frak(q))$, такую, что
  $alpha_2 #transpose($(a_1, dots, a_(n - 1))$, mark: $T$)
  = #transpose($(1, 0, dots, 0)$, mark: $T$)$. Таким образом, умножение #source(
    215,
  )слева на матрицу $overline(alpha)_2 = mat(alpha_2, 0; 0, I_2)$ приводит нас к
  той ситуации, когда для $alpha$ выполнено последнее условие, указанное в части
  @cond:linear-stability-last-column-reduction леммы, завершая тем самым
  доказательство @cond:linear-stability-last-column-reduction, что и
  требовалось.
]

#lemma[
  Предположим, что матрица $sigma in GL_(n + 1) (A, frak(q))$ имеет вид
  $sigma = overline(alpha) epsilon$, где $epsilon = I + a e_(n + 1, 1)$
  ($a in frak(q)$), $overline(alpha) = mat(alpha, gamma; 0, 1)$,
  $gamma = #transpose($(0, dots, 0, c)$, mark: $T$)$,
  $
    alpha = mat(
      1, a_12, dots, a_(1 n);
      0, a_22, dots, a_(2 n);
      dots.v, dots.v, , dots.v;
      0, dots, , dots;
      b, a_(n 2), dots, a_(n n)
    ).
  $
  Тогда $sigma in S$, т. е. $chi' (sigma^pi) = chi' (sigma)$.
] <lem:linear-stability-sparse-last-row>

Отметим сначала, что #emph[лемма @lem:linear-stability-sparse-last-row завершает
  доказательство теоремы @th:linear-character-extension-stability и,
  следовательно, теоремы @th:relative-k1-stability]. Действительно, как мы уже
показали, @th:linear-character-extension-stability $=>$
@th:relative-k1-stability, а из предположений теоремы
@th:linear-character-extension-stability следует предположение
@ss:linear-character-symmetric-stability. Условие $SR_n (A, frak(q))$ может быть
выполнено лишь для $n >= 2$, и поэтому такое ограничение на $n$ безобидно. Кроме
того, все предположения в лемме
@lem:linear-stability-transposition-invariance
@cond:linear-stability-last-column-reduction входят в предположения теоремы
@th:linear-character-extension-stability. Следовательно, в силу
@lem:linear-stability-transposition-invariance для доказательства равенства
$S = GL_(n + 1) (A, frak(q))$ достаточно показать, что $sigma in S$, как только
$sigma$ — матрица вида, указанного в @lem:linear-stability-sparse-last-row.
Таким образом, лемма @lem:linear-stability-sparse-last-row действительно
завершает доказательство теоремы @th:linear-character-extension-stability.

#proof(head: [Доказательство леммы @lem:linear-stability-sparse-last-row.])[
  В силу определения отображения $chi'$ справедливо равенство
  $chi' (sigma) = chi (alpha)$. С целью экономии места при записи матриц мы
  будем представлять их разбитыми на блоки:
  $
    alpha = mat(
      1, alpha_12, alpha_13; 0, alpha_22, alpha_23;
      b, alpha_32, alpha_33
    ), "где" alpha_22 = (a_(i j))_(2 <= i, j <= n - 1),
  $
  а остальные обозначения ясны. Положим
  $
    alpha' = mat(
      alpha_22, alpha_23;
      alpha_32 - b alpha_12, alpha_33 - b alpha_13
    ).
  $
  #source(216)Тогда
  $
    alpha equiv mat(
      1, alpha_12, alpha_13; 0, alpha_22, alpha_23;
      0, alpha_32 - b alpha_12, alpha_33 - b alpha_13
    )
    equiv mat(alpha', 0; 0, 1) mod overline(E)_n (A, frak(q)),
  $
  и поэтому
  $ chi' (sigma) = chi (alpha) = chi (mat(alpha', 0; 0, 1)). $
  <eq:linear-stability-reduced-character>
  Выделим затем
  $
    sigma = overline(alpha) epsilon
    = mat(alpha, gamma; 0, I) (I + a e_(n + 1, 1))
    = mat(
      1, alpha_12, alpha_13, 0; 0, alpha_22, alpha_23, 0;
      b + c a, alpha_32, alpha_33, c; a, 0, 0, 1
    ).
  $
  Так как отображение $sigma |-> sigma^pi$ как раз переставляет две последние
  строки и два последних столбца, то
  $
    sigma^pi = mat(
      1, alpha_12, 0, alpha_13; 0, alpha_22, 0, alpha_23;
      a, 0, 1, 0; d, alpha_32, c, alpha_33
    ) quad (d = b + c a).
  $
  Можем записать в стандартной форме
  $sigma^pi = (I + a e_(n 1)) (I + d e_(n + 1, 1)) overline(beta)$, где
  $
    overline(beta) = mat(1, rho; 0, beta)
    = mat(
      1, alpha_12, 0, alpha_13; 0, alpha_22, 0, alpha_23;
      0, -a alpha_12, 1, -a alpha_13;
      0, alpha_32 - d alpha_12, c, alpha_33 - d alpha_13
    ).
  $
  Таким образом,
  $ chi' (sigma^pi) = chi (I_n + a e_(n 1)) chi (beta) = chi (beta). $
  Чтобы вычислить $chi (beta)$, можем заменить $beta$ на любую матрицу,
  конгруэнтную с $beta$ по модулю $overline(E)_n (A, frak(q))$. Все следующие
  далее конгруэнции рассматриваются по модулю $overline(E)_n (A, frak(q))$.
  Заметим, что
  $
    beta = mat(
      alpha_22, 0, alpha_23; -a alpha_12, 1, -a alpha_13;
      alpha_32 - d alpha_12, c, alpha_33 - d alpha_13
    )
    equiv mat(
      alpha_22, 0, alpha_23; -a alpha_12, 1, -a alpha_13;
      alpha_32 + (c a - d) alpha_12, 0,
      alpha_33 + (c a - d) alpha_13
    ).
  $
  Напомним, что $d = b + c a$ и потому $c a - d = -b$.

  #source(217)Следовательно,
  $
    beta equiv mat(
      alpha_22, 0, alpha_23; -a alpha_12, 1, -a alpha_13;
      alpha_32 - b alpha_12, 0, alpha_33 - b alpha_13
    )
    equiv mat(
      alpha_22, 0, alpha_23; 0, 1, 0;
      alpha_32 - b alpha_12, 0, alpha_33 - b alpha_13
    )
    equiv mat(alpha', 0; 0, 1),
  $
  где $alpha' = mat(
    alpha_22, alpha_23;
    alpha_32 - b alpha_12, alpha_33 - b alpha_13
  )$ — та же самая матрица $alpha'$, которая появляется в
  @eq:linear-stability-reduced-character. Из
  @eq:linear-stability-reduced-character следует, таким образом, что
  $chi' (sigma^pi) = chi (beta) = chi (mat(alpha', 0; 0, 1)) = chi' (sigma)$.
  Доказательство завершено.
]
