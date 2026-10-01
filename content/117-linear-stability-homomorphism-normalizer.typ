#import "diagrams/stable-linear-groups-opposite-character.typ": (
  diagram-opposite-character,
)
#import "diagrams/stable-linear-groups-opposite-ring.typ": diagram-opposite-ring
#import "main-defs.typ": E, GE, GL, Ker, SR, U, diag, source, transpose
#import "statements.typ": (
  condition-item, condition-list, corollary, hypothesis, lemma, proof,
  proposition,
)

#heading(level: 2)[Доказательство теоремы @th:relative-k1-stability: II.
  Нормализатор гомоморфизма $chi'$]
<sec:linear-stability-homomorphism-normalizer>

Пусть $A^o$ — кольцо, противоположное кольцу $A$; переход к транспонированной
матрице является парой взаимно обратных антиизоморфизмов

#diagram-opposite-ring()

#source(209)Пусть $C^o$ — противоположная группа для группы $C$ (из утверждения
@ss:linear-character-extension). Тогда рассмотрим гомоморфизм
$chi^o: GL_n (A^o, frak(q)) -> C^o$, определенный условием коммутативности
диаграммы

#diagram-opposite-character()

т.~е. $chi^o (alpha) = chi(#transpose($alpha$, mark: $T$))$ как отображения
множеств. Чтобы избежать недоразумений, будем писать точку для обозначения
произведения в $GL_m (A^o)$ или в $C^o$. Например, если $x, y in C$, то
$x dot y = y x$.

Всюду в этом параграфе будем считать, что выполнено следующее

#hypothesis[
  Условия $SR_(n + 1)$, $SR'_n$ и $SR''_n$ выполнены для $(A, frak(q))$ и
  $(A^o, frak(q))$.
] <ss:linear-character-symmetric-stability>

При этом предположении справедливы все утверждения предложения
@prop:linear-standard-form-character относительно отображений $chi$ и $chi^o$.
Таким образом, получим отображение $chi'$ из
@prop:linear-standard-form-character, продолжающее отображение $chi$, и
аналогично определенное отображение $chi'^o$ (с помощью стандартной формы в
группе $GL_(n + 1) (A^o, frak(q))$), продолжающее отображение $chi^o$. В силу
симметрии наших предположений все определения и предложения относительно $chi'$
обладают аналогами для $chi'^o$.

Важно отметить, #emph[что из предположений теоремы
  @th:linear-character-extension-stability следует справедливость предположения
  @ss:linear-character-symmetric-stability.] Действительно, в предположение
теоремы @th:linear-character-extension-stability входят условия
$SR_n (A, frak(q))$, $SR_n (A^o, frak(q))$ и $SR'_(n - 1) (A, frak(q))$. Но для
всех $m >= n$ из $SR_n$ следует $SR'_m$ (см.
@th:stable-rank-relative-elementary-stability
@cond:stable-rank-elementary-transitivity) и из $SR_n$ следует $SR''_m$ (см.
@th:stable-rank-relative-elementary-stability
@cond:stable-rank-linked-matrix-equivalence). В силу этого замечания все
рассуждения этого параграфа образуют разумный вклад в доказательство теоремы
@th:linear-character-extension-stability. Более сильные предположения теоремы
@th:linear-character-extension-stability будут действовать лишь в
§~@sec:linear-stability-final-proof (см.
@lem:linear-stability-transposition-invariance
@cond:linear-stability-last-column-reduction и
@lem:linear-stability-sparse-last-row).

Наконец, заметим для применений в гл.~@ch:mennicke-symbols, что предположение
$SR''_n$ присутствует лишь для того, чтобы можно было воспользоваться
утверждением предложения @prop:linear-standard-form-character. Следовательно,
можно заменить условие $SR''_n$ на условие относительно отображения $chi$,
описанное в @rem:linear-character-linked-matrix-invariance, и тогда все
результаты этого параграфа останутся справедливыми.

Рассмотрим группы
$
  H = {sigma in GL_(n + 1) (A, frak(q)) |
    chi'(sigma sigma') = chi'(sigma) chi'(sigma')
    "для всех" sigma' in GL_(n + 1) (A, frak(q))}
$
и
$
  N = {tau in GL_(n + 1) (A) |
    chi'(sigma^tau) = chi'(sigma)
    "для всех" sigma in GL_(n + 1) (A, frak(q))}.
$

#source(210)Тот факт, что это группы, вытекает из следующего утверждения.

#lemma[
  #condition-list[
    #condition-item(format: "cyrillic")[$H$ является подгруппой, содержащей все
      матрицы типа $L$ из $GL_(n + 1) (A, frak(q))$.]
    <cond:linear-character-multiplicative-subgroup>

    #condition-item(format: "cyrillic")[$N$ является подгруппой группы
      $GL_(n + 1) (A)$, и $N$ нормализует подгруппу $H$.]
    <cond:linear-character-normalizer-subgroup>

    #condition-item(format: "cyrillic")[Пусть $K$ — подгруппа группы
      $GL_(n + 1) (A, frak(q))$, содержащая все матрицы типа $L$ и нормализуемая
      группой $E_(n + 1) (A)$. Тогда $K = GL_(n + 1) (A, frak(q))$.]
    <cond:linear-type-l-elementary-generation>
  ]
] <lem:linear-character-multiplicativity-normalizer>

#proof[
  Если $sigma in H$, то
  $1 = chi'(I) = chi'(sigma sigma^(-1)) = chi'(sigma) chi'(sigma^(-1))$, поэтому
  $chi'(sigma^(-1)) = chi'(sigma)^(-1)$. Теперь если
  $sigma' in GL_(n + 1) (A, frak(q))$, то
  $chi'(sigma') = chi'(sigma sigma^(-1) sigma')
  = chi'(sigma) chi'(sigma^(-1) sigma')$ и потому
  $chi'(sigma^(-1) sigma') = chi'(sigma)^(-1) chi'(sigma')
  = chi'(sigma^(-1)) chi'(sigma')$. Это показывает, что $sigma^(-1) in H$. Если
  $sigma_1, sigma_2 in H$, то для любой матрицы $sigma'$, рассмотренной выше,
  имеем $chi'(sigma_1 sigma_2 sigma') = chi'(sigma_1) chi'(sigma_2 sigma')
  = chi'(sigma_1) chi'(sigma_2) chi'(sigma')
  = chi'(sigma_1 sigma_2) chi'(sigma')$ и, значит, $sigma_1 sigma_2 in H$. Таким
  образом, $H$ — группа. То, что группа $H$ содержит все матрицы типа $L$,
  следует из @prop:linear-standard-form-character
  @cond:linear-standard-form-equivariance.

  @cond:linear-character-normalizer-subgroup Пусть
  $sigma in GL_(n + 1) (A, frak(q))$. Если $tau in N$, то
  $chi'(sigma^(tau^(-1))) = chi'((sigma^(tau^(-1)))^tau) = chi'(sigma)$, поэтому
  $tau^(-1) in N$. Если $tau_1, tau_2 in N$, то
  $chi'(sigma^(tau_1 tau_2)) = chi'(sigma^(tau_1)) = chi'(sigma)$, так что
  $tau_1 tau_2 in N$. Таким образом, $N$ — группа. Допустим, что $tau in N$ и
  $sigma_1 in H$. Тогда
  $chi'(sigma_1^tau sigma) = chi'((sigma_1 sigma^(tau^(-1)))^tau)
  = chi'(sigma_1 sigma^(tau^(-1))) = chi'(sigma_1) chi'(sigma^(tau^(-1)))
  = chi'(sigma_1^tau) chi'(sigma)$, и поэтому $sigma_1^tau in H$. Таким образом,
  $N$ нормализует подгруппу $H$.

  @cond:linear-type-l-elementary-generation Пусть
  $E = {I + t e_(1 2) | t in frak(q)}$. Очевидно, что $E subset K$, так как все
  матрицы $I + t e_(1 2)$ являются элементами типа $L$. Группа
  $GL_n (A, frak(q))$ (как подгруппа группы $GL_(n + 1) (A, frak(q))$) состоит
  из матриц типа $L$. Кроме того, нормальный делитель группы $E_(n + 1) (A)$,
  порожденный подгруппой $E$, совпадает с $E_(n + 1) (A, frak(q))$.
  Следовательно, предположения о подгруппе $K$ влекут за собой, что $K$ содержит
  $E_(n + 1) (A, frak(q)) dot GL_n (A, frak(q))$. Но в силу условия
  $SR_(n + 1) (A, frak(q))$ из предложения
  @prop:relative-linear-normal-subgroup-stability следует, что последнее
  множество матриц совпадает с $GL_(n + 1) (A, frak(q))$, что и требовалось
  доказать.
]

#corollary[
  Если $E_(n + 1) (A) subset N$, то $chi'$ — гомоморфизм, ядро которого содержит
  $E_(n + 1) (A, frak(q))$, и, следовательно, утверждение
  @ss:linear-character-extension установлено.
] <cor:linear-character-elementary-normalizer-extension>

#proof[
  Если $E_(n + 1) (A) subset N$, то из
  @lem:linear-character-multiplicativity-normalizer следует, что
  $H = GL_(n + 1) (A, frak(q))$, т.~е. что $chi'$ является гомоморфизмом. Кроме
  того, $Ker(chi') supset Ker(chi) supset E_n (A, frak(q))$, и $Ker(chi')$
  нормализуется группой $E_(n + 1) (A)$, а потому
  $Ker(chi') supset E_(n + 1) (A, frak(q))$, что и требовалось доказать.
]

В силу этого следствия дальнейшие наши усилия будут направлены на то, чтобы
доказать включение $E_(n + 1) (A) subset N$.

#source(211)#lemma[
  Группа $N$ содержит все матрицы вида
  $
    tau = mat(u, *, *; 0, gamma, *; 0, 0, v),
  $
  где $u, v in U(A)$ и $gamma in GE_(n - 1) (A)$, в предположении, что $n >= 2$.
  Если $n = 1$, то $N$ все же содержит группу $D_2 (A)$.
] <lem:linear-character-triangular-normalizer>

#proof[
  Указанные матрицы образуют группу, порожденную матрицами следующих типов:
  $
    tau_0 = diag(u_1, dots, u_(n + 1)) in D_(n + 1) (A); quad
    tau_1 = mat(1, 0, 0; 0, gamma, 0; 0, 0, 1),
  $
  где $gamma in E_(n - 1) (A)$; $tau_2 = I + t e_(i j)$, где $(i, j) = (1, 2)$
  или $(n, n + 1)$.

  Пусть $sigma = overline(alpha) epsilon overline(beta)$ — стандартная форма
  матрицы $sigma in GL_(n + 1) (A, frak(q))$. Тогда если $tau = tau_0$ или
  $tau_1$, то легко видеть, что
  $sigma^tau = overline(alpha)^tau epsilon^tau overline(beta)^tau$ — стандартная
  форма. Кроме того, так как $chi$ нормализуется группой $GE_n (A)$ (это было
  одним из предположений об отображении $chi$ в @ss:linear-character-extension),
  то легко следует, что $chi'(sigma^tau) = chi'(sigma)$. Эту несложную выкладку
  мы оставляем читателю.

  Предположим затем, что, скажем, $tau = I + t e_(1 2)$. Тогда матрица $tau$
  является одновременно элементом типа $L$ и типа $R$. Следовательно,
  $overline(alpha)^tau$ и $overline(beta)^tau$ — матрицы типа $L$ и $R$
  соответственно, $chi'(overline(alpha)^tau) = chi'(overline(alpha))$ и
  $chi'(overline(beta)^tau) = chi'(overline(beta))$.

  Теперь вспомним о предположении $n >= 2$. Если $epsilon = I + s e_(n + 1, 1)$,
  то $epsilon^tau = I + s e_(n + 1, 1) + s t e_(n + 1, 2)
  = epsilon overline(beta)_1$, где $overline(beta)_1 = I + s t e_(n + 1, 2)$ —
  матрица типа $R$ и $chi'(overline(beta)_1) = 1$. Следовательно,
  $sigma^tau = overline(alpha)^tau epsilon
  (overline(beta)_1 overline(beta)^tau)$ — стандартная форма матрицы
  $sigma^tau$. Из @prop:linear-standard-form-character
  @cond:linear-standard-form-equivariance вытекает, что
  $chi'(sigma^tau) = chi'(overline(alpha)^tau) chi'(overline(beta)_1)
  chi'(overline(beta)^tau) = chi'(overline(alpha)) chi'(overline(beta))
  = chi'(sigma)$.

  Рассуждения в случае $tau = I + t e_(n, n + 1)$ аналогичны, за исключением
  того, что на этот раз $epsilon^tau = overline(alpha)_1 epsilon$, где
  $overline(alpha)_1$ — матрица типа $L$ и $chi'(overline(alpha)_1) = 1$.
  Опустим детали доказательства.
]

Используем теперь отображение $chi'^o: GL_(n + 1) (A^o, frak(q)) -> C^o$,
описанное в начале этого параграфа. Можно рассмотреть аналог группы $N$:
$
  N^o = {tau in GL_(n + 1) (A^o) | chi'^o (sigma^tau) = chi'^o (sigma)
    "для всех" sigma in GL_(n + 1) (A^o, frak(q))}.
$
Так как наши предположения о кольцах $A$ и $A^o$ симметричны, можно применить
результаты, доказанные для $N$, также к $N^o$.

Пусть $phi = mat(0, 0, 1; 0, I_(n - 1), 0; 1, 0, 0)$, и заметим, что
$phi = #transpose($phi$, mark: $T$) = phi^(-1) in GE_(n + 1) (A)$
#source(212) (или соответственно $GE_(n + 1) (A^o)$). Для матрицы
$sigma in GL_(n + 1) (A)$ положим
$
  tilde(sigma) = phi dot #transpose($sigma$, mark: $T$) dot phi
  = (#transpose($sigma$, mark: $T$))^phi
  = #transpose($(sigma^phi)$, mark: $T$) in GL_(n + 1) (A^o).
$
Тогда отображение $sigma |-> tilde(sigma)$ является антиизоморфизмом (меняет
местами первую и последнюю строки и столбцы, а затем производит
транспонирование).

#lemma[
  Если $tau in GL_(n + 1) (A)$ и $tilde(tau) in N^o$, то $tau in N$.
] <lem:linear-character-opposite-normalizer>

#proof[
  Пусть $sigma = overline(alpha) epsilon overline(beta)$ — стандартная форма
  матрицы $sigma in GL_(n + 1) (A, frak(q))$. Тогда покажем, что
  $tilde(sigma) = tilde(overline(beta)) dot tilde(epsilon)
  dot tilde(overline(alpha))$ — стандартная форма матрицы $tilde(sigma)$ в
  $GL_(n + 1) (A^o, frak(q))$. Действительно, если
  $overline(alpha) = mat(alpha, gamma; 0, 1)$, то
  $tilde(overline(alpha)) = mat(1, gamma'; 0, alpha')$, где матрица $alpha'$
  получена из $#transpose($alpha$, mark: $T$)$ циклической перестановкой строк и
  столбцов, т.~е. $alpha' = (#transpose($alpha$, mark: $T$))^(pi^(-1))$, где
  $pi = mat(0, I_(n - 1); 1, 0) in GE_n$. Аналогично
  $tilde(overline(beta)) = mat(beta', rho'; 0, 1)$, где
  $beta' = (#transpose($beta$, mark: $T$))^pi$. Наконец,
  $tilde(epsilon) = epsilon$ (напомним, что $epsilon$ — матрица вида
  $I + t e_(n + 1, 1)$). Таким образом, можно вычислить
  $chi'^o (tilde(sigma)) = chi^o (beta') dot chi^o (alpha')$. Так как $chi^o$
  нормализуется группой $#transpose($GE_n (A)$, mark: $T$) = GE_n (A^o)$, то
  $chi^o (beta') = chi^o (#transpose($beta$, mark: $T$))$ и
  $chi^o (alpha') = chi^o (#transpose($alpha$, mark: $T$))$. Следовательно,
  $chi'^o (tilde(sigma)) = chi^o (#transpose($beta$, mark: $T$))
  dot chi^o (#transpose($alpha$, mark: $T$))
  = chi(alpha) chi(beta) = chi'(sigma)$.

  Теперь если $tilde(tau) in N^o$, то
  $chi'(sigma^tau) = chi'^o (tilde(sigma^tau))
  = chi'^o (tilde(sigma)^(tilde(tau)^(-1)))
  = chi'^o (tilde(sigma)) = chi'(sigma)$. Таким образом, $tau in N$, что и
  требовалось доказать.
]

#lemma[
  Допустим, что $n >= 2$. Положим
  $
    pi = mat(I_(n - 1), 0, 0; 0, 0, 1; 0, 1, 0).
  $
  Если $pi in N$, то $E_(n + 1) (A) subset N$.
] <lem:linear-character-permutation-normalizer>

#proof[
  В силу @lem:linear-character-triangular-normalizer группа $N$ содержит все
  матрицы вида $I + t e_(i j)$ $(t in A, i != j, i != n + 1, j != 1)$. В силу
  симметрии группа $N^o$ содержит все матрицы вида $I + t e_(i j)$
  $(t in A^o, i != j, i != n + 1, j != 1)$, и поэтому из леммы
  @lem:linear-character-opposite-normalizer следует, что $N$ содержит все
  матрицы $tau = I + t e_(i j)$, для которых матрица $tilde(tau)$ имеет
  описанный выше вид.

  Положим $tau_0 = I + e_(n, n + 1) in N$. В силу предположения $pi in N$,
  значит, $tau_0^pi = I + e_(n + 1, n) in N$. Если $tau = I + t e_(n j)$
  $(j != 1, n, n + 1)$, #source(213)то
  $[tau_0^pi, tau] = [I + e_(n + 1, n), I + t e_(n j)]
  = I + t e_(n + 1, j) in N$. Таким образом, для порождения всей группы
  $E_(n + 1) (A)$ нам недостает лишь элементарных матриц с недиагональными
  элементами в первом столбце. Для $1 < j < n + 1$ мы знаем, что
  $tilde(I + t e_(j 1)) = I + t e_(n + 1, j) in N^o$, поэтому в силу первого
  абзаца $I + t e_(j 1)$ принадлежат $N$. Теперь нам недостает лишь образующих
  $I + t e_(n + 1, 1)$. Но мы получим их из уже полученных по формуле
  $
    [I + e_(n + 1, n), I + t e_(n 1)] = I + t e_(n + 1, 1).
  $
  Лемма доказана.
]

Теперь соберем вместе утверждения этого параграфа.

#proposition[
  Сохраним предположение @ss:linear-character-symmetric-stability и допустим,
  далее, что $n >= 2$ и что
  $
    chi'(sigma^pi) = chi'(sigma)
    quad "для всех" sigma in GL_(n + 1) (A, frak(q)),
  $ <eq:linear-character-permutation-invariance>
  где $pi = mat(I_(n - 1), 0, 0; 0, 0, 1; 0, 1, 0)$. Тогда $chi'$ является
  гомоморфизмом, продолжающим отображение $chi$, и $E_(n + 1) (A, frak(q))$
  лежит в $Ker(chi')$, чем устанавливается справедливость утверждения
  @ss:linear-character-extension.
] <prop:linear-character-normalizer-criterion>

Это следует из @cor:linear-character-elementary-normalizer-extension и
@lem:linear-character-permutation-normalizer. В следующем параграфе мы получим
доказательство теоремы @th:relative-k1-stability, установив справедливость
приведенного выше условия @eq:linear-character-permutation-invariance в
предположениях, несколько более сильных, чем
@ss:linear-character-symmetric-stability. В гл.~@ch:mennicke-symbols мы еще раз
воспользуемся предложением @prop:linear-character-normalizer-criterion, но уже в
ситуации, где эти более сильные предположения не выполняются. Это объясняет
тщательность выбора наших предположений.
