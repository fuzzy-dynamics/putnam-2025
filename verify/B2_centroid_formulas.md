# Centroid Formula Verification for Putnam 2025 B2

## 1. Centroid of 2D Region

### Definition
For a planar region $R$, the centroid $(\bar{x}, \bar{y})$ is given by:

$$\bar{x} = \frac{1}{A} \iint_R x \, dA$$

$$\bar{y} = \frac{1}{A} \iint_R y \, dA$$

where $A = \iint_R dA$ is the area.

### Our Region
$R$ is bounded by:
- $x = 0$ (left)
- $x = 1$ (right)
- $y = 0$ (bottom)
- $y = f(x)$ (top)

### Computing the x-coordinate

The area is:
$$A = \int_0^1 \int_0^{f(x)} dy \, dx = \int_0^1 f(x) \, dx$$

The first moment about the y-axis:
$$M_y = \iint_R x \, dA = \int_0^1 \int_0^{f(x)} x \, dy \, dx = \int_0^1 x f(x) \, dx$$

Therefore:
$$\bar{x} = x_1 = \frac{M_y}{A} = \frac{\int_0^1 x f(x) \, dx}{\int_0^1 f(x) \, dx}$$

**VERIFIED:** This matches the solution. ✓

### Verification with simple case: $f(x) = 1$ (rectangle)

For a rectangle $[0,1] \times [0,1]$:
$$x_1 = \frac{\int_0^1 x \cdot 1 \, dx}{\int_0^1 1 \, dx} = \frac{1/2}{1} = \frac{1}{2}$$

This is correct - the centroid of a unit square is at $(1/2, 1/2)$. ✓

## 2. Centroid of Solid of Revolution

### Method: Disk/Washer Method

When rotating the region $R$ about the x-axis, we get a solid of revolution.

At position $x \in [0,1]$, we have a disk of:
- Radius: $r(x) = f(x)$
- Thickness: $dx$
- Volume: $dV = \pi [f(x)]^2 \, dx$

### Computing the x-coordinate

Total volume:
$$V = \int_0^1 \pi [f(x)]^2 \, dx$$

First moment about the $yz$-plane (i.e., about $x = 0$):
$$M_{yz} = \int_0^1 x \, dV = \int_0^1 x \cdot \pi [f(x)]^2 \, dx$$

Centroid:
$$\bar{x} = x_2 = \frac{M_{yz}}{V} = \frac{\int_0^1 x \cdot \pi [f(x)]^2 \, dx}{\int_0^1 \pi [f(x)]^2 \, dx} = \frac{\int_0^1 x [f(x)]^2 \, dx}{\int_0^1 [f(x)]^2 \, dx}$$

**VERIFIED:** This matches the solution. ✓

### Verification with simple case: $f(x) = R$ (cylinder)

For a cylinder of radius $R$ and length 1:
$$x_2 = \frac{\int_0^1 x \cdot R^2 \, dx}{\int_0^1 R^2 \, dx} = \frac{R^2 \cdot 1/2}{R^2 \cdot 1} = \frac{1}{2}$$

This is correct - the centroid of a cylinder is at its midpoint. ✓

### Verification with $f(x) = x$ (cone)

For a cone with base radius 1 and height 1:
- Volume: $V = \frac{1}{3}\pi (1)^2 (1) = \frac{\pi}{3}$
- Using the disk method: $V = \int_0^1 \pi x^2 \, dx = \pi \cdot \frac{1}{3} = \frac{\pi}{3}$ ✓

Centroid x-coordinate:
$$x_2 = \frac{\int_0^1 x \cdot x^2 \, dx}{\int_0^1 x^2 \, dx} = \frac{\int_0^1 x^3 \, dx}{\int_0^1 x^2 \, dx} = \frac{1/4}{1/3} = \frac{3}{4}$$

Known result: The centroid of a cone is at distance $\frac{3}{4}$ from the apex (along the axis). ✓

This confirms our formula is correct!

## 3. Summary

Both centroid formulas used in the solution are correct:

1. **2D region:** $x_1 = \frac{\int_0^1 x f(x) \, dx}{\int_0^1 f(x) \, dx}$ ✓

2. **Solid of revolution:** $x_2 = \frac{\int_0^1 x [f(x)]^2 \, dx}{\int_0^1 [f(x)]^2 \, dx}$ ✓

Both formulas have been verified against:
- Standard calculus definitions
- Special cases with known answers
- Numerical computation for various functions
