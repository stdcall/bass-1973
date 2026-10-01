#import "main-defs.typ": E, GE, GL, Ker, SR, idx, source, transpose
#import "statements.typ": (
  assertion, condition-item, condition-list, numbered-condition, proof,
  proposition, remark, theorem,
)

#heading(level: 2)[Доказательство теоремы @th:relative-k1-stability: I.
  Конструкция гомоморфизма $chi'$]
<sec:linear-stability-homomorphism-construction>

В следующих трех параграфах будут фиксированы кольцо $A$ и двусторонний идеал
$frak(q)$.

Напомним (см. §~@sec:stable-rank-conditions), что
$
  overline(E)_m (A, frak(q))
$
является группой, порожденной группами $E_m (A, frak(q))$ и
$[GE_m (A), GL_m (A, frak(q))]$. Таким образом, например, из
@cor:relative-elementary-commutators вытекает, что
$
  overline(E)_m (A, frak(q)) = [GE_m (A), GL_m (A, frak(q))]
  quad "при" m >= 3.
$ <eq:extended-elementary-group-commutator>
С другой стороны, из @prop:relative-linear-normal-subgroup-stability и
@th:linear-normal-subgroup-stability следует, что

#numbered-condition[
  _Если кольцо $A$ удовлетворяет условию $SR_n (A, frak(q))$, то
  $overline(E)_m (A, frak(q)) = E_m (A, frak(q))$ для всех $m >= n$. При этом
  если кольцо $A$ удовлетворяет условию $SR_n (A)$, то получаем нормальный
  делитель группы $GL_m (A)$._
] <eq:extended-elementary-stable-rank>

Доказательство теоремы @th:relative-k1-stability будет сгруппировано вокруг
следующего предложения, которое справедливо при соответствующих предположениях:

#assertion(parameter: "n")[
  Если нам дан гомоморфизм $chi: GL_n (A, frak(q)) -> C$, такой, что
  $overline(E)_n (A, frak(q)) subset Ker(chi)$, то существует гомоморфизм
  $chi': GL_(n + 1) (A, frak(q)) -> C$, продолжающий гомоморфизм $chi$ и такой,
  что $overline(E)_(n + 1) (A, frak(q)) subset Ker(chi')$.
] <ss:linear-character-extension>

Докажем, в частности, следующее утверждение:

#theorem[
  Если выполнены условия $SR_n (A, frak(q))$, $SR_n (A^o, frak(q))$ и
  $SR'_(n - 1) (A, frak(q))$, то справедливо утверждение
  @ss:linear-character-extension.
] <th:linear-character-extension-stability>

#proof(head: [Доказательство импликации @th:linear-character-extension-stability
  $=>$ @th:relative-k1-stability.])[
  Если $m >= n$, то рассмотрим естественный гомоморфизм
  $chi_m: GL_m (A, frak(q)) -> C_m (frak(q))
  = GL_m (A, frak(q)) slash E_m (A, frak(q))$
  (см. приведенное утверждение @eq:extended-elementary-stable-rank). Для
  $m >= n$ рассмотрим естественные гомоморфизмы
  $S_m: C_n (frak(q)) -> C_m (frak(q))$. Из @th:linear-normal-subgroup-stability
  @cond:linear-relative-elementary-normality следует, что эти отображения
  сюръективны и даже что отображение $GL_(n - 1) (A, frak(q)) -> C_m (frak(q))$
  также сюръективно. Для завершения доказательства #source(205)теоремы
  @th:relative-k1-stability, таким образом, нам надо показать, что все
  отображения $S_m$ являются изоморфизмами.

  В силу теоремы @th:linear-character-extension-stability можно применить
  утверждение @ss:linear-character-extension к гомоморфизму $chi_n$. Полученное
  таким образом отображение $chi'$ индуцирует гомоморфизм
  $C_(n + 1) (frak(q)) -> C_n (frak(q))$, являющийся обратным для гомоморфизма
  $S_(n + 1)$. Так как
  $[SR_n (A, frak(q))] => [SR_m (A, frak(q)) "и" SR'_m (A, frak(q))$
  (см. @th:stable-rank-relative-elementary-stability) $"для всех" m >= n]$ и
  аналогичная импликация имеет место для кольца $A^o$, то, проводя индукцию по
  $m - n$, мы можем закончить доказательство.
]

В доказательстве утверждения @ss:linear-character-extension все, кроме
последнего этапа, можно вывести из более слабых предположений, чем в
@th:linear-character-extension-stability. Эта дополнительная общность будет
использована в §~@sec:semilocal-linear-groups, а также в
гл.~@ch:mennicke-symbols.

#emph[В
  §~@sec:linear-stability-homomorphism-construction–@sec:linear-stability-final-proof
  через $chi: GL_n (A, frak(q)) -> C$ будем обозначать фиксированный гомоморфизм
  из утверждения @ss:linear-character-extension.]

Будем называть элемент группы $GL_m (A)$ элементом типа $L$, если его последняя
строка равна $(0, dots, 0, 1)$ и типа $R$, если его первый столбец равен
$#transpose($(1, 0, dots, 0)$, mark: $T$)$. Например, элемент типа $L$ выглядит
так:
$
  overline(alpha) = mat(alpha, gamma; 0, 1),
$
где $alpha in GL_(m - 1) (A)$, $#transpose($gamma$, mark: $T$) in A^(m - 1)$ и
т.~д. Аналогично элемент типа $R$ можно записать в виде
$
  overline(beta) = mat(1, rho; 0, beta).
$
Если $sigma in GL_m (A, frak(q))$, то _стандартной формой_ элемента $sigma$#idx(
  "стандартная форма элемента",
) назовем разложение
$
  sigma = overline(alpha) epsilon overline(beta),
$ <eq:linear-standard-form>
где все сомножители лежат в $GL_m (A, frak(q))$ и $overline(alpha)$ и
$overline(beta)$ — элементы типа $L$ и $R$ соответственно и где
$epsilon = I + t e_(m 1)$ для некоторого элемента $t in frak(q)$. (Фактически
элемент $t$ должен быть $(m, 1)$-элементом матрицы $sigma$.)

Эти понятия понадобятся нам, конечно, временно. Важность их здесь объясняется
следующим предложением.

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[Допустим, что выполнены условия
      $SR_(n + 1) (A, frak(q))$ и $SR'_n (A, frak(q))$. Тогда каждый элемент
      $sigma in GL_(n + 1) (A, frak(q))$ можно записать в стандартной форме
      $sigma = overline(alpha) epsilon overline(beta)$ (как в формуле
      @eq:linear-standard-form).]
    <cond:linear-standard-form-existence>

    Предположим, далее, что выполнено условие $SR''_n (A, frak(q))$. Тогда

    #condition-item(format: "cyrillic")[отображение
      $
        chi': GL_(n + 1) (A, frak(q)) -> C,
      $
      #source(206)для которого $chi'(sigma) = chi(alpha) chi(beta)$, если
      элемент $sigma = overline(alpha) epsilon overline(beta)$ записан в
      стандартной форме, определено корректно и продолжает отображение $chi$;]
    <cond:linear-standard-form-character>

    #condition-item(format: "cyrillic")[если $overline(alpha)_1$,
      $overline(beta)_1 in GL_(n + 1) (A, frak(q))$ — элементы типа $L$ и $R$
      соответственно, то
      $
        chi'(overline(alpha)_1 sigma overline(beta)_1)
        = chi'(overline(alpha)_1) chi'(sigma) chi'(overline(beta)_1);
      $
    ] <cond:linear-standard-form-equivariance>

    #condition-item(format: "cyrillic")[если существует гомоморфизм
      $chi'': GL_(n + 1) (A, frak(q)) -> C$, продолжающий отображение $chi$ и
      такой, что $E_(n + 1) (A, frak(q)) subset Ker(chi'')$, то $chi'' = chi'$.]
    <cond:linear-standard-form-character-uniqueness>
  ]
] <prop:linear-standard-form-character>

При доказательстве утверждения @ss:linear-character-extension мы по ходу дела
покажем (усиливая предположения в @prop:linear-standard-form-character), что
построенный выше гомоморфизм $chi'$ отображает
$overline(E)_(n + 1) (A, frak(q))$ в единицу.

#proof[
  #condition-list[
    #condition-item(format: "cyrillic")[Пусть $sigma_1 = #transpose(
        $(a_1, dots, a_(n + 1))$,
        mark: $T$,
      )$ — первый столбец матрицы $sigma$. Используя условие
      $SR_(n + 1) (A, frak(q))$, найдем матрицу
      $overline(gamma) = mat(I, -gamma; 0, 1) in E_(n + 1) (A, frak(q))$, такую,
      что $overline(gamma) sigma_1 = #transpose(
        $(b_1, dots, b_n, a_(n + 1))$,
        mark: $T$,
      )$, где строка $sigma'_1 = #transpose($(b_1, dots, b_n)$, mark: $T$)$
      является $frak(q)$-унимодулярной. В силу условия $SR'_n (A, frak(q))$,
      найдется матрица $alpha in GL_n (A, frak(q))$, такая, что
      $alpha^(-1) sigma'_1 = #transpose($(1, 0, dots, 0)$, mark: $T$)$. Положим
      $overline(alpha)_1 = mat(alpha^(-1), 0; 0, 1)$. Тогда
      $overline(alpha)_1 overline(gamma) sigma_1
      = #transpose($(1, 0, dots, 0, a_(n + 1))$, mark: $T$)$. Положим
      $epsilon = I + a_(n + 1) e_(n + 1, 1)$. Тогда первый столбец матрицы
      $overline(beta) = epsilon^(-1) overline(alpha)_1 overline(gamma) sigma$
      равен $#transpose($(1, 0, dots, 0)$, mark: $T$)$, т.~е. $overline(beta)$ —
      элемент типа $R$. Тогда $sigma = overline(alpha) epsilon overline(beta)$,
      где
      $
        overline(alpha) = overline(gamma)^(-1) overline(alpha)_1^(-1)
        = mat(I, gamma; 0, 1) mat(alpha, 0; 0, 1)
        = mat(alpha, gamma; 0, 1),
      $
      что и требовалось доказать.] <cond:linear-standard-form-existence-proof>

    #condition-item(format: "cyrillic")[Пусть
      $sigma = overline(alpha)_1 epsilon overline(beta)_1
      = overline(alpha)_2 epsilon overline(beta)_2$ — две стандартные формы
      матрицы $sigma$. (Как мы заметили, матрица $epsilon$ определяется матрицей
      $sigma$ ($(n + 1, 1)$-элементом).) Запишем
      $
        overline(alpha)_i = mat(alpha_i, gamma_i; 0, 1), quad
        overline(beta)_i = mat(1, rho_i; 0, beta_i) quad (i = 1, 2).
      $
      Мы должны показать, что $chi(alpha_1) chi(beta_1)
      = chi(alpha_2) chi(beta_2)$. Так как отображение $chi$ — гомоморфизм, то
      это равносильно равенству $chi(alpha) = chi(beta)$, где
      $alpha = alpha_1^(-1) alpha_2$ и $beta = beta_1 beta_2^(-1)$. Выведем его
      из равенства
      $
        overline(alpha) epsilon = epsilon overline(beta); quad
        overline(alpha) = overline(alpha)_1^(-1) overline(alpha)_2
        = mat(alpha, gamma; 0, 1),
        overline(beta) = overline(beta)_1 overline(beta)_2^(-1)
        = mat(1, rho; 0, beta).
      $
      Запишем $alpha = (a_(i j))$, $beta = (b_(i j))$, $gamma = #transpose(
        $(c_1, dots, c_n)$,
        mark: $T$,
      )$ и $rho = (r_1, dots, r_n)$. #source(207)Тогда
      $
        overline(alpha) epsilon = mat(
          a_11 + c_1 t, a_12, dots.h, a_(1 n), c_1;
          dots.v, dots.v, , dots.v, dots.v;
          a_(n 1) + c_n t, a_(n 2), dots.h, a_(n n), c_n;
          t, 0, dots.h, 0, 1
        )
      $
      и
      $
        epsilon overline(beta) = mat(
          1, r_1, dots.h, r_n;
          0, b_11, dots.h, b_(1 n);
          dots.v, dots.v, , dots.v;
          0, b_(n - 1, 1), dots.h, b_(n - 1, n);
          t, b_(n 1) + t r_1, dots.h, b_(n n) + t r_n
        ).
      $
      Положим $a = c_1$ (что также равно $r_n$). Тогда
      $
        alpha = mat(1 - a t, alpha_12; -alpha_21 t, alpha_22),
      $
      где $alpha_12 = (a_12, dots, a_(1 n)) = (r_1, dots, r_(n - 1))$,
      $alpha_21 = #transpose($(c_2, dots, c_n)$, mark: $T$)$ и
      $alpha_22 = (a_(i j))_(2 <= i, j <= n)
      = (b_(i j))_(1 <= i, j <= n - 1)$. Мы получаем, таким образом, что
      $
        beta = mat(alpha_22, alpha_21; -t alpha_12, 1 - t a).
      $
      Положим $pi = mat(0, 1; I_(n - 1), 0) in GE_n (A)$ (матрица подстановки
      $i |-> i + 1 (mod n)$). Тогда
      $
        beta^(pi^(-1)) = pi beta pi^(-1)
        = mat(1 - t a, -t alpha_12; alpha_21, alpha_22).
      $
      Таким образом, $alpha$ — элемент типа $(frak(q), -t)$ (см.
      @def:relative-stable-rank), и матрица $beta^(pi^(-1))$
      $(frak(q), -t)$-связана с $alpha$. Из условия $SR''_n (A, frak(q))$
      следует, что если матрица $alpha'$ $(frak(q), -t)$-связана с $alpha$, то
      $alpha' alpha^(-1) in overline(E)_n (A, frak(q))$. Так как
      $overline(E)_n (A, frak(q)) subset Ker(chi)$ (по предположению), то из
      этого следует, что $chi(alpha) = chi(alpha')$. В частности,
      $chi(beta^(pi^(-1))) = chi(alpha)$. Так как
      $beta^(-1) beta^(pi^(-1)) = [beta, pi^(-1)]
      in overline(E)_n (A, frak(q))$, то к тому же
      $chi(beta) = chi(beta^(pi^(-1)))$, и поэтому $chi(alpha) = chi(beta)$. Это
      показывает, что отображение $chi'$ определено корректно. Если
      $overline(alpha) = mat(alpha, 0; 0, 1) in GL_(n + 1) (A, frak(q))$, то
      $overline(alpha)$ — элемент типа $L$, и поэтому
      $chi'(overline(alpha)) = chi(alpha)$, т.~е. $chi'$ продолжает отображение
      $chi$, что и требовалось
      доказать.] <cond:linear-standard-form-character-proof>

    #source(208)#remark[
      Последний этап приведенного доказательства — единственное место в наших
      рассуждениях, где было использовано условие $SR''_n (A, frak(q))$. Для
      удобства ссылок в будущем сформулируем следующее замечание (очевидное в
      силу проведенных рассуждений):
      _предложение @prop:linear-standard-form-character остается справедливым,
      если заменить условие $SR''_n (A, frak(q))$ на предположение о том, что
      $chi(alpha) = chi(alpha')$, если только для некоторого $t in frak(q)$
      $alpha in GL_n (A, frak(q))$ — элемент типа $(frak(q), t)$ и матрица
      $alpha'$ $(frak(q), t)$-связана с $alpha$._
    ] <rem:linear-character-linked-matrix-invariance>

    #condition-item(format: "cyrillic")[Пусть
      $sigma = overline(alpha) epsilon overline(beta)$ — стандартная форма для
      $sigma in GL_(n + 1) (A, frak(q))$, и пусть
      $
        overline(alpha)_1 = mat(alpha_1, gamma_1; 0, 1), quad
        overline(beta)_1 = mat(1, rho_1; 0, beta_1)
      $
      — элементы группы $GL_(n + 1) (A, frak(q))$. Тогда
      $overline(alpha)_1 sigma overline(beta)_1
      = (overline(alpha)_1 overline(alpha)) epsilon
      (overline(beta) overline(beta)_1)$ — стандартная форма, где
      $
        overline(alpha)_1 overline(alpha) = mat(alpha_1 alpha, *; 0, 1),
        quad overline(beta) overline(beta)_1 = mat(1, *; 0, beta beta_1).
      $
      Следовательно,
      $
        chi'(overline(alpha)_1 sigma overline(beta)_1)
        = chi(alpha_1 alpha) chi(beta beta_1)
        = chi(alpha_1) chi(alpha) chi(beta) chi(beta_1)
        = chi'(overline(alpha)_1) chi'(sigma) chi'(overline(beta)_1),
      $
      что и требовалось
      доказать.] <cond:linear-standard-form-equivariance-proof>

    #condition-item(format: "cyrillic")[Пусть
      $chi'': GL_(n + 1) (A, frak(q)) -> C$ — гомоморфизм, продолжающий
      отображение $chi$ и отображающий $E_(n + 1) (A, frak(q))$ в единицу. В
      силу @prop:relative-linear-normal-subgroup-stability и нашего условия
      $SR_(n + 1) (A, frak(q))$ справедливо равенство
      $GL_(n + 1) (A, frak(q)) = E_(n + 1) (A, frak(q)) dot GL_n (A, frak(q))$.
      Следовательно, отображение $chi''$ определено однозначно приведенными
      условиями. Если $sigma = overline(alpha) epsilon overline(beta)$ —
      стандартная форма, то $chi''(epsilon) = 1$. Так как
      $overline(alpha) = mat(I, gamma; 0, 1) mat(alpha, 0; 0, 1)$, то
      $chi''(overline(alpha)) = chi(alpha)$. Наконец,
      $overline(beta) = mat(I, 0; 0, beta) mat(1, rho; 0, I)$, и первый
      сомножитель является матрицей, сопряженной (при помощи матрицы
      перестановки) с $mat(beta, 0; 0, 1)$. Таким образом,
      $chi''(overline(beta)) = chi(beta)$, поскольку
      $[GE_(n + 1) (A), GL_(n + 1) (A, frak(q))] subset E_(n + 1) (A, frak(q))$
      (см. @eq:extended-elementary-stable-rank выше). Это показывает, что
      $chi'' = chi'$, доказывая @cond:linear-standard-form-character-uniqueness
      и завершая доказательство предложения
      @prop:linear-standard-form-character.]
    <cond:linear-standard-form-uniqueness-proof>
  ]
]
