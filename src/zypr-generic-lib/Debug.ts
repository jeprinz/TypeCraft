const __debug_level = 0

export function debug(level: number, ...xs: any[]) {
    if (level <= __debug_level)
        console.log(...["[>]"].concat(xs))
}

export function debug_(level: number, ...xs: any[]) { }