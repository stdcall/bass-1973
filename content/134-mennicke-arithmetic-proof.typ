#import "main-defs.typ": E, GL, Ker, SL, SR, diag, dim, mennicke, source

#heading(level: 2)[Доказательство теоремы @th:universal-mennicke-symbol-sk1. II.
  Заключительная часть] <sec:mennicke-arithmetic-proof>

Гомоморфизм $k: GL_2 (A, frak(q)) -> C$, построенный в теореме Куботы
@ss:kubota-mennicke-homomorphism, см. также § @sec:kubotas-theorem, надо
расширить до гомоморфизма $k': GL_3 (A, frak(q)) -> C$, для которого
$E_3 (A, frak(q)) subset Ker(k')$. Как мы видели в §
@sec:mennicke-main-theorems, этим будет завершено доказательство
@th:universal-mennicke-symbol-sk1. Можно, конечно, предполагать, что
$frak(q) != 0$.

Так как $dim A <= 1$ и кольцо $A$ коммутативно, то выполнены условия стабильного
ранга $SR_3 (A, frak(q))$ (см. @th:stable-rank-dimension-bound) и
$SR'_2 (A, frak(q))$ (см. #source(246) @prop:semilocal-commutative-stable-rank
@cond:commutative-rank-two-transitivity). Кроме того, гомоморфизм $k$
удовлетворяет условию из @rem:linear-character-linked-matrix-invariance (см.
часть @cond:kubota-matrix-transfer доказательства теоремы Куботы). Таким
образом, из @rem:linear-character-linked-matrix-invariance следует, что
существует отображение $k': GL_3 (A, frak(q)) -> C$, продолжающее гомоморфизм
$k$ и определенное с помощью «стандартной формы». Именно если

$ sigma = mat(alpha, gamma; 0, 1)(I + t e_(3 1)) mat(1, rho; 0, beta) $

и все сомножители лежат в группе $GL_3 (A, frak(q))$, то
$k'(sigma) = k(alpha) k(beta)$. Кроме того, все результаты
@ch:stable-linear-groups, § @sec:linear-stability-homomorphism-normalizer,
применимы к отображению $k'$, в частности применимо предложение
@prop:linear-character-normalizer-criterion. Наиболее существенный момент: для
доказательства того, что $k'$ — гомоморфизм, ядро которого содержит
$E_3 (A, frak(q))$, достаточно убедиться в том, что

$ k'(sigma^pi) = k'(sigma) $ <eq:mennicke-extension-permutation-invariance>

для всех $sigma in GL_3 (A, frak(q))$, где

$ pi = mat(1, 0, 0; 0, 0, 1; 0, 1, 0). $

Далее, из @lem:linear-stability-transposition-invariance следует, что достаточно
проверить @eq:mennicke-extension-permutation-invariance для
$sigma = overline(alpha) epsilon$, где $overline(alpha)$,
$epsilon in GL_3 (A, frak(q))$ — матрицы вида

$
  overline(alpha) = mat(alpha, gamma; 0, 1), quad
  alpha = mat(a_(1 1), a_(1 2); a_(2 1), a_(2 2)), quad
  gamma = vec(0, c), quad epsilon = I + t e_(3 1).
$

По @lem:linear-stability-transposition-invariance
@cond:linear-stability-type-l-r-reduction можно предварительно заменить $sigma$
на $lambda sigma$, где
$lambda = diag((det alpha)^(-1), 1, 1) in GL_3 (A, frak(q))$. При этом
$gamma = vec(0, c)$ сохраняется, а определитель $alpha$ становится равным $1$.

В силу @lem:linear-stability-transposition-invariance мы можем заменить матрицу
$sigma$ на $tau sigma$, где $tau = I + q e_(1 2)$ ($q in frak(q)$). Таким
образом, можно добиться того, чтобы $a_(1 1) != 0$.

Но

$ sigma = mat(a_(1 1), a_(1 2), 0; a_(2 1) + t c, a_(2 2), c; t, 0, 1) $

и

$ sigma^pi = mat(a_(1 1), 0, a_(1 2); t, 1, 0; a_(2 1) + t c, c, a_(2 2)). $

Так как кольцо $frac(A, a_(1 1) A)$ полулокально, то существует элемент
$s in frak(q)$, такой, что элементы $t + s(a_(2 1) + t c)$ и $a_(1 1)$
комаксимальны. Так как $s$ определен лишь по модулю $a_(1 1) frak(q)$, то можно,
далее, выбрать элемент $s$ так, чтобы $d = 1 + s c != 0$. Заметим, что
$t + s(a_(2 1) + t c) = s a_(2 1) + t d$.

#source(247)Положим $delta = I + s e_(2 3)$. Тогда

$
  delta sigma^pi = mat(
    a_(1 1), 0, a_(1 2);
    s a_(2 1) + t d, d, s a_(2 2); a_(2 1) + t c, c, a_(2 2)
  ).
$

Так как $(a_(1 1), s a_(2 1) + d t) in W_frak(q)$ (в силу построения), то
найдется матрица $omega = mat(w_(1 1), w_(1 2); w_(2 1), w_(2 2))
in SL_2 (A, frak(q))$, такая, что

$ omega mat(a_(1 1), 0; s a_(2 1) + t d, d) = mat(1, x; 0, y) $
<eq:mennicke-extension-unimodular-reduction>

для некоторых $x, y in A$. Пусть $overline(omega) = mat(omega, 0; 0, 1)$. Тогда

$
  overline(omega) delta sigma^pi = mat(
    1, x,
    w_(1 1) a_(1 2) + w_(1 2) s a_(2 2);
    0, y, w_(2 1) a_(1 2) + w_(2 2) s a_(2 2);
    a_(2 1) + t c, c, a_(2 2)
  ).
$

Пусть $u = a_(2 1) + t c$. Положим $epsilon_1 = I + u e_(3 1)$. Имеем
$overline(beta) = epsilon_1^(-1) overline(omega) delta sigma^pi
= mat(1, rho; 0, beta)$, где

$
  beta = mat(
    y, w_(2 1) a_(1 2) + w_(2 2) s a_(2 2);
    c - u x, a_(2 2) - u(w_(1 1) a_(1 2) + w_(1 2) s a_(2 2))
  ).
$

Но $sigma^pi = (delta^(-1) overline(omega)^(-1)) epsilon_1 overline(beta)$ —
стандартная форма матрицы $sigma^pi$, поскольку

$
  delta^(-1) overline(omega)^(-1)
  = mat(omega^(-1), vec(0, -s); 0, 1)
$

— матрица типа $L$ (см. @ch:stable-linear-groups, §
@sec:linear-stability-homomorphism-construction). Таким образом,

$ k'(sigma^pi) = k(omega)^(-1) k(beta), $

и мы должны доказать, что это равно

$ k'(sigma) = k(alpha) = mennicke(a_(1 2), a_(1 1)). $

Запишем равенство @eq:mennicke-extension-unimodular-reduction более подробно:

$
  mat(
    w_(1 1) a_(1 1) + w_(1 2)(s a_(2 1) + t d), w_(1 2) d;
    w_(2 1) a_(1 1) + w_(2 2)(s a_(2 1) + t d), w_(2 2) d
  )
  = mat(1, x; 0, y).
$

Так как $det(omega) = 1$, то определитель левой части
@eq:mennicke-extension-unimodular-reduction равен $a_(1 1) d$, и поэтому
$y = a_(1 1) d$. Таким образом, $w_(2 2) d = a_(1 1) d$. Так как $d != 0$ (в
силу приведенного построения), то можно заключить, что #source(
  248,
)$w_(2 2) = a_(1 1)$. Учитывая это в равенстве для $(2, 1)$-координаты, можно
опять сократить на $a_(1 1)$ и получить, что $w_(2 1) = -s a_(2 1) - t d$. Таким
образом, $(1, 2)$-координата матрицы $beta$ равна
$-(s a_(2 1) + t d) a_(1 2) + a_(1 1) s a_(2 2)
= s(a_(1 1) a_(2 2) - a_(1 2) a_(2 1)) - t d a_(1 2)
= s - t d a_(1 2)$, и потому

$ beta = mat(a_(1 1) d, s - t d a_(1 2); ast, ast). $

С другой стороны,

$ omega = mat(w_(1 1), w_(1 2); -(s a_(2 1) + t d), a_(1 1)), $

где, напомним, $d = 1 + s c$. Теперь мы можем вычислить $k(omega)^(-1) k(beta)$.
Заметим, что

$
  k(omega)^(-1) = mennicke(-(s a_(2 1) + t d), a_(1 1))^(-1)
  = mennicke(-(s a_(2 1) + t d), a_(1 1))^(-1)
  mennicke(a_(1 2), a_(1 1))^(-1) k(alpha)
  = k(alpha) mennicke(-s a_(1 2) a_(2 1) - t d a_(1 2), a_(1 1))^(-1)
  = k(alpha) mennicke(s(1 - a_(1 1) a_(2 2)) - t d a_(1 2), a_(1 1))^(-1)
  = k(alpha) mennicke(s - t d a_(1 2), a_(1 1))^(-1).
$

Далее,

$
  k(beta) = mennicke(s - t d a_(1 2), a_(1 1) d)
  = mennicke(s - t d a_(1 2), a_(1 1)) mennicke(s - t d a_(1 2), d)
  = mennicke(s - t d a_(1 2), a_(1 1)) mennicke(s, d)
  = mennicke(s - t d a_(1 2), a_(1 1)),
$

поскольку $d = 1 + s c$. Таким образом, действительно
$k(omega)^(-1) k(beta) = k(alpha)$, что и требовалось доказать.
