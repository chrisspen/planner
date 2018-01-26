
def print_board(state):
    """
    Prints the board state in a 3x3 grid.
    """
    board = ['.']*9
    for fact in state.facts:
        if fact.data['a'].startswith('pos') and fact.data['v'] != 'e':
            pos = int(fact.data['a'][-1])
            v = fact.data['v']
            board[pos] = v
    print '-'*80
    for i in xrange(3):
        print ''.join(board[i*3:i*3+3])

game_uuid = lambda: 'game0'

def _get_winner(b):
    """
    Returns the color of the winner.
    """
    if b[0] == b[1] == b[2]:
        return b[0]
    if b[3] == b[4] == b[5]:
        return b[3]
    if b[6] == b[7] == b[8]:
        return b[6]
    if b[0] == b[3] == b[6]:
        return b[0]
    if b[1] == b[4] == b[7]:
        return b[1]
    if b[2] == b[5] == b[8]:
        return b[2]
    if b[0] == b[4] == b[8]:
        return b[0]
    if b[2] == b[4] == b[6]:
        return b[2]

def label_state(game, turn, mycolor):
    """
    Switch the aggregator per state in a Minimax-fashion by maximizing the
    expected fitness if it's our turn and minimizing expected fitness if it's
    our opponent's turn.
    """
    if turn == mycolor:
        return dict(expected_fitness_default=0,
                    expected_fitness_aggregator=max)
    else:
        return dict(expected_fitness_default=+1e999999,
                    expected_fitness_aggregator=min)

def fitness(**kwargs):
    """
    Returns close to 0.0 for a late loss.
    Returns close to 1.0 for an early win.
    """
    board = []
    for i in xrange(9):
        board.append(kwargs['c%i' % i])

    turn = kwargs['turn']

    mycolor = kwargs['mycolor']

    moves = int(kwargs['moves'])

    winner = _get_winner(board)

    score = (winner == mycolor)*0.9 + (1-moves/9.)*0.1
    return score
