export function zip<X, Y>(xs: X[], ys: Y[]): [X, Y][] {
    var zs: [X, Y][] = []
    for (var i = 0; i < Math.min(xs.length, ys.length); i++)
        zs.push([xs[i], ys[i]])
    return zs
}