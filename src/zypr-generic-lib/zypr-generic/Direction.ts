export type Direction
    = { case: 'up' }
    | { case: 'down', i: number }
    | { case: 'left' }
    | { case: 'right' }
    | { case: 'next' } | { case: 'prev' }