# Optimización de la Constante de Hardy Discreta en el Cubo RS^N³

## 1. Diagnóstico del límite $\lambda = 1/20$ en `HardyVF.lean`

En `HardyVF.lean`, la desigualdad polinomial se planteó de forma desacoplada eje por eje (`axis_poly`):
$$1/10 / (x^2 + q) - 1/4 \cdot x^2 / (x^2 + q)^2 \le 2\kappa_i(p) - 2\kappa_i(p - e_i) - 2\kappa_i(p)^2 - 2\kappa_i(p - e_i)^2$$

Para acotar el término cuadrático $-2\kappa_i^2$, se utilizó la cota:
$$\kappa_i(p)^2 = \mu^2 \frac{(x_i + 1/2)^2}{((x_i + 1/2)^2 + q)^2} \le \mu^2 \frac{1}{(x_i + 1/2)^2 + q} \quad \left(\text{usando } \frac{(x_i + 1/2)^2}{(x_i + 1/2)^2 + q} \le 1\right)$$

### Pérdida del factor 3
Físicamente, $\kappa_i^2 \approx \mu^2 \frac{x_i^2}{R^4}$. Al sumar los 3 ejes:
$$\sum_{i=0}^2 \kappa_i^2 \approx \mu^2 \frac{\sum x_i^2}{R^4} = \frac{\mu^2}{R^2}$$
Al descartar $x_i^2/R^2 \le 1$ en cada eje por separado, la suma sobre los 3 ejes restó:
$$\sum_{i=0}^2 \frac{\mu^2}{R^2} = \frac{\mathbf{3}\mu^2}{R^2}$$
Con 2 aristas dirigidas por eje y el factor 2 en $2\kappa^2$, la penalización total fue $12\mu^2$ en lugar de $4\mu^2$.

### Teorema del Techo Desacoplado
La divergencia suma $2\mu / R^2$. Con la disipación inflada a $12\mu^2$, el balance asintótico desacoplado es:
$$\lambda \le 2\mu - 12\mu^2$$
El máximo ocurre en $\mu = 1/12 \approx 0.0833$, donde $\lambda_{\max} \le 1/12 \approx 0.0833$.
Con $\mu = 1/16$, $\lambda = 1/20 = 0.05$. Ningún ajuste de coeficientes eje por eje puede superar $1/12$.

---

## 2. Geometría 3D Real en la Red: Mínimo $\lambda = 0.19313$

Al evaluar el campo vectorial tridimensional completo:
$$w_{\mathrm{VF}}(p) = \sum_{i=0}^2 \left( 2\kappa_i(p) - 2\kappa_i(p - e_i) - 2\kappa_i(p)^2 - 2\kappa_i(p - e_i)^2 \right)$$
con $\mu = 0.20$ (o $\mu = 0.21$):

* **Celda central** $(1/2, 1/2, 1/2)$ ($R^2 = 0.75$):
  $$w_{\mathrm{VF}} \cdot R^2 = \mathbf{0.52000}$$
* **Primeros vecinos**:
  * $(1.5, 0.5, 0.5)$ ($R^2 = 2.75$): $w_{\mathrm{VF}} \cdot R^2 = \mathbf{0.20697}$
  * $(1.5, 1.5, 0.5)$ ($R^2 = 4.75$): $w_{\mathrm{VF}} \cdot R^2 = \mathbf{0.28242}$
* **Punto de inflexión / Mínimo global de toda la red infinita**:
  * $(2.5, 0.5, 0.5)$ ($R^2 = 6.75$):
    $$w_{\mathrm{VF}} \cdot R^2 = \mathbf{0.19291}$$
* **Límite asintótico** ($R \to \infty$):
  $$w_{\mathrm{VF}} \cdot R^2 \to 2\mu - 4\mu^2 = 2(0.20) - 4(0.04) = \mathbf{0.24000}$$

### Consecuencia Física
Tomando $\lambda = \frac{3}{16} = 0.1875$ (o $0.19$):
$$E_0 \ge -\frac{k^2}{2 \lambda} = -\frac{k^2}{2 (3/16)} = -\frac{8}{3} k^2 \approx \mathbf{-2.667 k^2}$$
Mejora de casi $4\times$ frente a $-10 k^2$, acercándose al nivel fundamental de Rydberg ($-0.5$).

---

## 3. Identidad Exacta para la Formalización en Lean

El denominador en cada arista se simplifica de forma exacta porque el término longitudinal y la distancia transversal $q_i = R^2 - x_i^2$ colapsan:
$$D_{i, +} = (x_i + 1/2)^2 + q_i = R^2 + x_i + 1/4$$
$$D_{i, -} = (x_i - 1/2)^2 + q_i = R^2 - x_i + 1/4$$
$$D_i = D_{i, +} D_{i, -} = (R^2 + 1/4)^2 - x_i^2$$

### Divergencia
$$2(\kappa_i(p) - \kappa_i(p - e_i)) = 2\mu \frac{R^2 + 1/4 - 2x_i^2}{D_i}$$
Sumando sobre $i \in \{0, 1, 2\}$, los numeradores se combinan constructivamente:
$$\sum_{i=0}^2 (R^2 + 1/4 - 2x_i^2) = 3 R^2 + \frac{3}{4} - 2 \sum x_i^2 = \mathbf{R^2 + \frac{3}{4}}$$

### Disipación
$$2(\kappa_i(p)^2 + \kappa_i(p - e_i)^2) = 4\mu^2 \frac{x_i^2 (R^2 - 1/4)^2 + \frac{1}{4}(R^2 + 1/4 - 2x_i^2)^2}{D_i^2}$$
Sumando sobre $i \in \{0, 1, 2\}$, el término cuadrático dominante es:
$$\sum_{i=0}^2 x_i^2 (R^2 - 1/4)^2 = \mathbf{R^2 (R^2 - 1/4)^2}$$
lo que colapsa la suma multivariable en la variable radial única $R^2$, permitiendo la prueba acoplada en Lean.
