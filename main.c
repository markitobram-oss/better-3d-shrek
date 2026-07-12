// Backrooms Ogre 3D - Nintendo DS homebrew
// First-person maze crawler using the DS's real 3D hardware (libnds GL).
// Grid-based movement with 90-degree turns (classic dungeon-crawler style),
// procedurally generated maze, distance fog, flickering lights, and a
// stalking monster that pathfinds toward you.
// Build with devkitARM + libnds (same pipeline as the earlier DS games)

#include <nds.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAZE_W 16
#define MAZE_H 12
#define NUM_CELLS (MAZE_W*MAZE_H)

#define WALL_N 1
#define WALL_E 2
#define WALL_S 4
#define WALL_W 8

#define WCELL 2.0f      // world size of one maze cell
#define WALLH 2.0f      // wall/ceiling height
#define EYE_Y 1.0f      // camera eye height

#define MOVE_FRAMES 12
#define TURN_FRAMES 8
#define RENDER_RADIUS 6

static u8 maze[MAZE_H][MAZE_W];
static int distField[MAZE_H][MAZE_W];

// facing: 0=N 1=E 2=S 3=W
static const int cellDX[4] = {0, 1, 0, -1};
static const int cellDY[4] = {-1, 0, 1, 0};
static const int wallBitForDir[4] = {WALL_N, WALL_E, WALL_S, WALL_W};
static const float dirVecX[4] = {0.0f, 1.0f, 0.0f, -1.0f};
static const float dirVecZ[4] = {-1.0f, 0.0f, 1.0f, 0.0f};

static int playerCX, playerCY;
static int facing;
static float playerWX, playerWZ;
static float moveFromWX, moveFromWZ, moveToWX, moveToWZ;
static int moveProgress;
static bool moving;

static float curDirX, curDirZ;
static float fromDirX, fromDirZ, toDirX, toDirZ;
static int turnProgress;
static bool turning;
static int stepParity; // alternates each completed move, for left/right foot animation

static int monsterCX, monsterCY;
static float monsterWX, monsterWZ;
static float monsterFromWX, monsterFromWZ;
static int monsterMoveTimer, monsterMoveInterval, monsterMoveProgress;

static int exitCX, exitCY;
static int level;
static bool gameStarted, gameOver;

static bool revealed[MAZE_H][MAZE_W];
static u16* fbSub;
#define MINICELL 9

static int flickerTimer;
static float flickerFactor;
static int doorFlashTimer;

// ---------------------------------------------------------------------
static void generateMaze(void) {
    for (int y = 0; y < MAZE_H; y++)
        for (int x = 0; x < MAZE_W; x++)
            maze[y][x] = WALL_N | WALL_E | WALL_S | WALL_W;

    static bool visited[MAZE_H][MAZE_W];
    memset(visited, 0, sizeof(visited));

    static int stackX[NUM_CELLS], stackY[NUM_CELLS];
    int sp = 0;
    int cx = 0, cy = 0;
    visited[cy][cx] = true;
    stackX[sp] = cx; stackY[sp] = cy; sp++;

    while (sp > 0) {
        cx = stackX[sp-1]; cy = stackY[sp-1];

        int dirs[4] = {0,1,2,3};
        for (int i = 3; i > 0; i--) {
            int j = rand() % (i+1);
            int tmp = dirs[i]; dirs[i] = dirs[j]; dirs[j] = tmp;
        }

        bool moved = false;
        for (int d = 0; d < 4; d++) {
            int dir = dirs[d];
            int nx = cx + cellDX[dir];
            int ny = cy + cellDY[dir];
            if (nx < 0 || nx >= MAZE_W || ny < 0 || ny >= MAZE_H) continue;
            if (visited[ny][nx]) continue;

            maze[cy][cx] &= ~wallBitForDir[dir];
            maze[ny][nx] &= ~wallBitForDir[(dir+2)%4];

            visited[ny][nx] = true;
            stackX[sp] = nx; stackY[sp] = ny; sp++;
            moved = true;
            break;
        }
        if (!moved) sp--;
    }
}

static void bfsDistance(int fromX, int fromY) {
    static int qx[NUM_CELLS], qy[NUM_CELLS];
    for (int y = 0; y < MAZE_H; y++)
        for (int x = 0; x < MAZE_W; x++)
            distField[y][x] = -1;

    int head = 0, tail = 0;
    qx[tail] = fromX; qy[tail] = fromY; tail++;
    distField[fromY][fromX] = 0;

    while (head < tail) {
        int cx = qx[head], cy = qy[head]; head++;
        int d = distField[cy][cx];
        u8 w = maze[cy][cx];
        for (int dir = 0; dir < 4; dir++) {
            if (w & wallBitForDir[dir]) continue;
            int nx = cx + cellDX[dir], ny = cy + cellDY[dir];
            if (nx < 0 || nx >= MAZE_W || ny < 0 || ny >= MAZE_H) continue;
            if (distField[ny][nx] >= 0) continue;
            distField[ny][nx] = d+1;
            qx[tail] = nx; qy[tail] = ny; tail++;
        }
    }
}

static void revealAround(int cx, int cy);

static void startLevel(void) {
    generateMaze();

    playerCX = 0; playerCY = 0;
    facing = 1; // start facing East
    playerWX = playerCX*WCELL + WCELL/2;
    playerWZ = playerCY*WCELL + WCELL/2;
    moving = false; moveProgress = MOVE_FRAMES;
    turning = false; turnProgress = TURN_FRAMES;
    curDirX = dirVecX[facing]; curDirZ = dirVecZ[facing];

    bfsDistance(playerCX, playerCY);

    int bestD = -1, bx = MAZE_W-1, by = MAZE_H-1;
    for (int y = 0; y < MAZE_H; y++)
        for (int x = 0; x < MAZE_W; x++)
            if (distField[y][x] > bestD) { bestD = distField[y][x]; bx = x; by = y; }
    exitCX = bx; exitCY = by;

    int candX = -1, candY = -1, tries = 0;
    while (tries < 200) {
        int rx = rand() % MAZE_W, ry = rand() % MAZE_H;
        if (distField[ry][rx] > bestD/3 && !(rx==exitCX && ry==exitCY) && !(rx==0 && ry==0)) {
            candX = rx; candY = ry; break;
        }
        tries++;
    }
    if (candX < 0) { candX = MAZE_W-1; candY = 0; }
    monsterCX = candX; monsterCY = candY;
    monsterWX = monsterCX*WCELL + WCELL/2;
    monsterWZ = monsterCY*WCELL + WCELL/2;
    monsterMoveTimer = 0;
    monsterMoveProgress = MOVE_FRAMES;
    monsterMoveInterval = level >= 6 ? 26 : (level >= 3 ? 34 : 44);

    flickerTimer = 0;
    flickerFactor = 1.0f;

    memset(revealed, 0, sizeof(revealed));
    revealAround(playerCX, playerCY);
}

static void resetGame(void) {
    level = 1;
    gameStarted = true;
    gameOver = false;
    startLevel();
}

static int distTier(int dx, int dy) {
    int d2 = dx*dx + dy*dy;
    if (d2 <= 1) return 0;
    if (d2 <= 4) return 1;
    if (d2 <= 9) return 2;
    if (d2 <= 16) return 3;
    if (d2 <= 25) return 4;
    return 5;
}
static const float tierFactor[6] = {1.0f, 0.82f, 0.62f, 0.44f, 0.28f, 0.16f};

// ---------------------------------------------------------------------
// Sub-screen (bottom screen) minimap
static void subPutPixel(int x, int y, u16 color) {
    if (x < 0 || x >= 256 || y < 0 || y >= 192) return;
    fbSub[y*256 + x] = color;
}
static void subFillRect(int x, int y, int w, int h, u16 color) {
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > 256) w = 256 - x;
    if (y + h > 192) h = 192 - y;
    if (w <= 0 || h <= 0) return;
    for (int row = 0; row < h; row++) {
        dmaFillHalfWords(color, &fbSub[(y+row)*256 + x], w*2);
    }
}

// Tiny 3x5 blocky digit font (bits, top-to-bottom rows, 3 bits per row, MSB-first)
static const u8 digitFont[10][5] = {
    {0b111,0b101,0b101,0b101,0b111}, // 0
    {0b010,0b110,0b010,0b010,0b111}, // 1
    {0b111,0b001,0b111,0b100,0b111}, // 2
    {0b111,0b001,0b111,0b001,0b111}, // 3
    {0b101,0b101,0b111,0b001,0b001}, // 4
    {0b111,0b100,0b111,0b001,0b111}, // 5
    {0b111,0b100,0b111,0b101,0b111}, // 6
    {0b111,0b001,0b001,0b001,0b001}, // 7
    {0b111,0b101,0b111,0b101,0b111}, // 8
    {0b111,0b101,0b111,0b001,0b111}, // 9
};
static void drawDigit(int x, int y, int d, int scale, u16 color) {
    if (d < 0 || d > 9) return;
    for (int row = 0; row < 5; row++) {
        u8 bits = digitFont[d][row];
        for (int col = 0; col < 3; col++) {
            if (bits & (1 << (2-col))) {
                subFillRect(x + col*scale, y + row*scale, scale, scale, color);
            }
        }
    }
}
static void drawNumber(int x, int y, int n, int scale, u16 color) {
    if (n < 0) n = 0;
    char buf[6];
    int len = 0;
    if (n == 0) { buf[len++] = 0; }
    else { int t = n; while (t > 0 && len < 5) { buf[len++] = t % 10; t /= 10; } }
    for (int i = 0; i < len; i++) {
        drawDigit(x + (len-1-i)*(3*scale+scale), y, buf[i], scale, color);
    }
}

static void initSubScreen(void) {
    videoSetModeSub(MODE_5_2D);
    vramSetBankC(VRAM_C_SUB_BG);
    int bgS = bgInitSub(3, BgType_Bmp16, BgSize_B16_256x256, 0, 0);
    fbSub = (u16*)bgGetGfxPtr(bgS);
}

static void revealAround(int cx, int cy) {
    revealed[cy][cx] = true;
    u8 w = maze[cy][cx];
    for (int dir = 0; dir < 4; dir++) {
        if (w & wallBitForDir[dir]) continue;
        int nx = cx + cellDX[dir], ny = cy + cellDY[dir];
        if (nx < 0 || nx >= MAZE_W || ny < 0 || ny >= MAZE_H) continue;
        revealed[ny][nx] = true;
    }
}

static void drawMinimap(void) {
    if (doorFlashTimer > 0 && (doorFlashTimer/3) % 2 == 0) {
        subFillRect(0, 0, 256, 192, RGB15(6,26,10)|0x8000);
        return;
    }

    subFillRect(0, 0, 256, 192, 0x8000); // opaque black background

    int originX = 6, originY = 6;
    u16 wallCol = RGB15(10,10,14)|0x8000;
    u16 floorCol = RGB15(4,4,6)|0x8000;
    u16 exitCol = RGB15(31,31,10)|0x8000;
    u16 playerCol = RGB15(10,28,10)|0x8000;
    u16 monsterCol = RGB15(28,4,4)|0x8000;

    for (int cy = 0; cy < MAZE_H; cy++) {
        for (int cx = 0; cx < MAZE_W; cx++) {
            if (!revealed[cy][cx]) continue;
            int x = originX + cx*MINICELL;
            int y = originY + cy*MINICELL;
            subFillRect(x, y, MINICELL-1, MINICELL-1, floorCol);
            u8 w = maze[cy][cx];
            if (w & WALL_N) subFillRect(x, y, MINICELL-1, 1, wallCol);
            if (w & WALL_S) subFillRect(x, y+MINICELL-2, MINICELL-1, 1, wallCol);
            if (w & WALL_W) subFillRect(x, y, 1, MINICELL-1, wallCol);
            if (w & WALL_E) subFillRect(x+MINICELL-2, y, 1, MINICELL-1, wallCol);

            if (cx == exitCX && cy == exitCY) {
                subFillRect(x+2, y+2, MINICELL-5, MINICELL-5, exitCol);
            }
        }
    }

    if (revealed[monsterCY][monsterCX]) {
        int mx = originX + monsterCX*MINICELL + MINICELL/2;
        int my = originY + monsterCY*MINICELL + MINICELL/2;
        subFillRect(mx-2, my-2, 4, 4, monsterCol);
    }

    int px = originX + playerCX*MINICELL + MINICELL/2;
    int py = originY + playerCY*MINICELL + MINICELL/2;
    subFillRect(px-2, py-2, 4, 4, playerCol);
    int ax = px + (int)(curDirX*6), ay = py + (int)(curDirZ*6);
    subFillRect(ax-1, ay-1, 2, 2, playerCol);

    // level number, bottom-right corner
    drawNumber(256-38, 192-16, level, 2, RGB15(20,20,20)|0x8000);
}

static void quad(float x0,float y0,float z0, float x1,float y1,float z1,
                  float x2,float y2,float z2, float x3,float y3,float z3,
                  float r,float g,float b) {
    glColor3f(r, g, b);
    glVertex3f(x0,y0,z0);
    glVertex3f(x1,y1,z1);
    glVertex3f(x2,y2,z2);
    glVertex3f(x3,y3,z3);
}

int main(void) {
    videoSetMode(MODE_0_3D);
    glInit();
    glEnable(GL_ANTIALIAS);
    glClearColor(0, 0, 0, 31);
    glClearPolyID(63);
    glClearDepth(0x7FFF);
    glViewport(0, 0, 255, 191);
    glPolyFmt(POLY_ALPHA(31) | POLY_CULL_NONE);

    consoleDemoInit();
    srand(21);

    gameStarted = false;
    gameOver = false;
    level = 1;
    startLevel();

    iprintf("\x1b[2J");
    iprintf("   BACKROOMS OGRE 3D\n\n");
    iprintf("   UP/DOWN: walk\n");
    iprintf("   LEFT/RIGHT: turn\n\n");
    iprintf("   Find the exit.\n");
    iprintf("   Something is\n");
    iprintf("   looking for you.\n\n");
    iprintf("   Press A to start\n");

    while (1) {
        scanKeys();
        int down = keysDown();

        if (!gameStarted && !gameOver) {
            if (down & KEY_A) { resetGame(); initSubScreen(); doorFlashTimer = 0; }
        } else if (gameOver) {
            if (down & KEY_A) { resetGame(); initSubScreen(); doorFlashTimer = 0; }
        } else if (gameStarted) {
            // ---- turning ----
            if (!turning && !moving) {
                if (down & KEY_LEFT) {
                    fromDirX = curDirX; fromDirZ = curDirZ;
                    facing = (facing + 3) % 4;
                    toDirX = dirVecX[facing]; toDirZ = dirVecZ[facing];
                    turning = true; turnProgress = 0;
                } else if (down & KEY_RIGHT) {
                    fromDirX = curDirX; fromDirZ = curDirZ;
                    facing = (facing + 1) % 4;
                    toDirX = dirVecX[facing]; toDirZ = dirVecZ[facing];
                    turning = true; turnProgress = 0;
                }
            }
            if (turning) {
                turnProgress++;
                float t = (float)turnProgress / TURN_FRAMES;
                curDirX = fromDirX + (toDirX - fromDirX)*t;
                curDirZ = fromDirZ + (toDirZ - fromDirZ)*t;
                if (turnProgress >= TURN_FRAMES) {
                    curDirX = toDirX; curDirZ = toDirZ;
                    turning = false;
                }
            }

            // ---- moving ----
            int held = keysHeld();
            if (!moving && !turning) {
                u8 w = maze[playerCY][playerCX];
                if (held & KEY_UP && !(w & wallBitForDir[facing])) {
                    moveFromWX = playerWX; moveFromWZ = playerWZ;
                    int nx = playerCX + cellDX[facing], ny = playerCY + cellDY[facing];
                    moveToWX = nx*WCELL + WCELL/2; moveToWZ = ny*WCELL + WCELL/2;
                    playerCX = nx; playerCY = ny;
                    moving = true; moveProgress = 0;
                    stepParity = !stepParity;
                } else if (held & KEY_DOWN && !(w & wallBitForDir[(facing+2)%4])) {
                    moveFromWX = playerWX; moveFromWZ = playerWZ;
                    int bd = (facing+2)%4;
                    int nx = playerCX + cellDX[bd], ny = playerCY + cellDY[bd];
                    moveToWX = nx*WCELL + WCELL/2; moveToWZ = ny*WCELL + WCELL/2;
                    playerCX = nx; playerCY = ny;
                    moving = true; moveProgress = 0;
                    stepParity = !stepParity;
                }
            }
            if (moving) {
                moveProgress++;
                float t = (float)moveProgress / MOVE_FRAMES;
                playerWX = moveFromWX + (moveToWX - moveFromWX)*t;
                playerWZ = moveFromWZ + (moveToWZ - moveFromWZ)*t;
                if (moveProgress >= MOVE_FRAMES) {
                    playerWX = moveToWX; playerWZ = moveToWZ;
                    moving = false;
                }
            }

            // ---- monster chase ----
            monsterMoveTimer++;
            if (monsterMoveTimer >= monsterMoveInterval && monsterMoveProgress >= MOVE_FRAMES) {
                monsterMoveTimer = 0;
                bfsDistance(playerCX, playerCY);
                int curD = distField[monsterCY][monsterCX];
                int bestNX = monsterCX, bestNY = monsterCY, bestD = curD;
                u8 mw = maze[monsterCY][monsterCX];
                for (int dir = 0; dir < 4; dir++) {
                    if (mw & wallBitForDir[dir]) continue;
                    int nx = monsterCX + cellDX[dir], ny = monsterCY + cellDY[dir];
                    if (distField[ny][nx] >= 0 && distField[ny][nx] < bestD) {
                        bestD = distField[ny][nx]; bestNX = nx; bestNY = ny;
                    }
                }
                if (bestNX != monsterCX || bestNY != monsterCY) {
                    monsterFromWX = monsterWX; monsterFromWZ = monsterWZ;
                    monsterCX = bestNX; monsterCY = bestNY;
                    monsterMoveProgress = 0;
                }
            }
            if (monsterMoveProgress < MOVE_FRAMES) {
                monsterMoveProgress++;
                float t = (float)monsterMoveProgress / MOVE_FRAMES;
                float toX = monsterCX*WCELL + WCELL/2, toZ = monsterCY*WCELL + WCELL/2;
                monsterWX = monsterFromWX + (toX - monsterFromWX)*t;
                monsterWZ = monsterFromWZ + (toZ - monsterFromWZ)*t;
            }

            // ---- flicker ----
            flickerTimer++;
            if (flickerTimer > 14) {
                flickerTimer = 0;
                int r = rand() % 10;
                if (r == 0) flickerFactor = 0.7f;
                else if (r == 1) flickerFactor = 0.88f;
                else flickerFactor = 1.0f;
            }

            // ---- reveal minimap around player as they explore ----
            revealAround(playerCX, playerCY);
            if (doorFlashTimer > 0) doorFlashTimer--;

            // ---- win/lose ----
            if (playerCX == exitCX && playerCY == exitCY) {
                level++;
                startLevel();
                doorFlashTimer = 20; // green flash cue on the minimap
            }
            if (monsterCX == playerCX && monsterCY == playerCY) {
                gameOver = true;
                gameStarted = false;
                consoleDemoInit();
                iprintf("\x1b[2J");
                iprintf("   IT FOUND YOU\n\n");
                iprintf("   Reached level %d\n\n", level);
                iprintf("   Press A to retry\n");
            }
        }

        // ---- render ----
        float bobY = 0.0f;
        if (moving) {
            int half = MOVE_FRAMES/2;
            int b = (moveProgress <= half) ? moveProgress : (MOVE_FRAMES - moveProgress);
            bobY = (b * 0.10f) / half;
        }
        float eyeY = EYE_Y + bobY;

        glMatrixMode(GL_MODELVIEW);
        glLoadIdentity();
        gluLookAt(
            playerWX, eyeY, playerWZ,
            playerWX + curDirX, eyeY, playerWZ + curDirZ,
            0.0f, 1.0f, 0.0f
        );

        if (gameStarted) {
            glBegin(GL_QUADS);

            float floorBase = 0.42f * flickerFactor;
            float wallBase  = 0.62f * flickerFactor;
            float ceilBase  = 0.34f * flickerFactor;

            int cx0 = playerCX - RENDER_RADIUS, cx1 = playerCX + RENDER_RADIUS;
            int cy0 = playerCY - RENDER_RADIUS, cy1 = playerCY + RENDER_RADIUS;
            if (cx0 < 0) cx0 = 0; if (cx1 >= MAZE_W) cx1 = MAZE_W-1;
            if (cy0 < 0) cy0 = 0; if (cy1 >= MAZE_H) cy1 = MAZE_H-1;

            for (int cy = cy0; cy <= cy1; cy++) {
                for (int cx = cx0; cx <= cx1; cx++) {
                    int dx = cx - playerCX, dy = cy - playerCY;
                    int tier = distTier(dx, dy);
                    if (tier >= 5) continue;
                    float f = tierFactor[tier];

                    float x0 = cx*WCELL, x1 = x0+WCELL;
                    float z0 = cy*WCELL, z1 = z0+WCELL;

                    bool isExit = (cx == exitCX && cy == exitCY);
                    float fr = isExit ? 0.9f*f : floorBase*f;
                    float fg = isExit ? (flickerTimer%28<14 ? 0.9f : 0.5f)*f : floorBase*0.95f*f;
                    float fb = isExit ? 0.6f*f : floorBase*0.5f*f;

                    quad(x0,0,z0, x1,0,z0, x1,0,z1, x0,0,z1, fr,fg,fb);
                    quad(x0,WALLH,z0, x0,WALLH,z1, x1,WALLH,z1, x1,WALLH,z0,
                         ceilBase*f, ceilBase*0.95f*f, ceilBase*0.7f*f);

                    u8 w = maze[cy][cx];
                    float wr = wallBase*f, wg = wallBase*0.9f*f, wb = wallBase*0.55f*f;
                    if (w & WALL_N) quad(x0,0,z0, x1,0,z0, x1,WALLH,z0, x0,WALLH,z0, wr,wg,wb);
                    if (w & WALL_S) quad(x1,0,z1, x0,0,z1, x0,WALLH,z1, x1,WALLH,z1, wr,wg,wb);
                    if (w & WALL_E) quad(x1,0,z0, x1,0,z1, x1,WALLH,z1, x1,WALLH,z0, wr,wg,wb);
                    if (w & WALL_W) quad(x0,0,z1, x0,0,z0, x0,WALLH,z0, x0,WALLH,z1, wr,wg,wb);
                }
            }

            // monster - simple billboard-ish quad aligned to nearest cardinal axis
            int mdx = monsterCX - playerCX, mdy = monsterCY - playerCY;
            int mtier = distTier(mdx, mdy);
            if (mtier < 5) {
                float mf = tierFactor[mtier];
                if (facing == 0 || facing == 2) {
                    quad(monsterWX-0.35f,0.15f,monsterWZ, monsterWX+0.35f,0.15f,monsterWZ,
                         monsterWX+0.35f,1.5f,monsterWZ, monsterWX-0.35f,1.5f,monsterWZ,
                         0.02f*mf,0.02f*mf,0.02f*mf);
                    quad(monsterWX-0.15f,1.05f,monsterWZ-0.02f, monsterWX-0.05f,1.05f,monsterWZ-0.02f,
                         monsterWX-0.05f,0.95f,monsterWZ-0.02f, monsterWX-0.15f,0.95f,monsterWZ-0.02f,
                         0.9f*mf,0.05f,0.05f);
                    quad(monsterWX+0.05f,1.05f,monsterWZ-0.02f, monsterWX+0.15f,1.05f,monsterWZ-0.02f,
                         monsterWX+0.15f,0.95f,monsterWZ-0.02f, monsterWX+0.05f,0.95f,monsterWZ-0.02f,
                         0.9f*mf,0.05f,0.05f);
                } else {
                    quad(monsterWX,0.15f,monsterWZ-0.35f, monsterWX,0.15f,monsterWZ+0.35f,
                         monsterWX,1.5f,monsterWZ+0.35f, monsterWX,1.5f,monsterWZ-0.35f,
                         0.02f*mf,0.02f*mf,0.02f*mf);
                    quad(monsterWX-0.02f,1.05f,monsterWZ-0.15f, monsterWX-0.02f,1.05f,monsterWZ-0.05f,
                         monsterWX-0.02f,0.95f,monsterWZ-0.05f, monsterWX-0.02f,0.95f,monsterWZ-0.15f,
                         0.9f*mf,0.05f,0.05f);
                    quad(monsterWX-0.02f,1.05f,monsterWZ+0.05f, monsterWX-0.02f,1.05f,monsterWZ+0.15f,
                         monsterWX-0.02f,0.95f,monsterWZ+0.15f, monsterWX-0.02f,0.95f,monsterWZ+0.05f,
                         0.9f*mf,0.05f,0.05f);
                }
            }

            // ---- first-person ogre body (belly + feet) ----
            {
                float rightX = -curDirZ, rightZ = curDirX;

                // belly
                float bfx = playerWX + curDirX*0.42f;
                float bfz = playerWZ + curDirZ*0.42f;
                float by0 = eyeY - 0.75f, by1 = eyeY - 0.30f;
                quad(bfx - rightX*0.22f, by0, bfz - rightZ*0.22f,
                     bfx + rightX*0.22f, by0, bfz + rightZ*0.22f,
                     bfx + rightX*0.22f, by1, bfz + rightZ*0.22f,
                     bfx - rightX*0.22f, by1, bfz - rightZ*0.22f,
                     0.10f, 0.30f, 0.10f);

                // left foot (bounces forward on alternating steps)
                float lfFwd = 0.30f + (stepParity ? bobY*1.4f : 0.0f);
                float lfx = playerWX + curDirX*lfFwd - rightX*0.16f;
                float lfz = playerWZ + curDirZ*lfFwd - rightZ*0.16f;
                quad(lfx - rightX*0.09f, 0.03f, lfz - rightZ*0.09f,
                     lfx + rightX*0.09f, 0.03f, lfz + rightZ*0.09f,
                     lfx + rightX*0.09f, 0.20f, lfz + rightZ*0.09f,
                     lfx - rightX*0.09f, 0.20f, lfz - rightZ*0.09f,
                     0.06f, 0.20f, 0.06f);

                // right foot (bounces forward on the opposite steps)
                float rfFwd = 0.30f + (stepParity ? 0.0f : bobY*1.4f);
                float rfx = playerWX + curDirX*rfFwd + rightX*0.16f;
                float rfz = playerWZ + curDirZ*rfFwd + rightZ*0.16f;
                quad(rfx - rightX*0.09f, 0.03f, rfz - rightZ*0.09f,
                     rfx + rightX*0.09f, 0.03f, rfz + rightZ*0.09f,
                     rfx + rightX*0.09f, 0.20f, rfz + rightZ*0.09f,
                     rfx - rightX*0.09f, 0.20f, rfz - rightZ*0.09f,
                     0.06f, 0.20f, 0.06f);
            }

            glEnd();

            drawMinimap();
        }

        glFlush(0);
        swiWaitForVBlank();
    }

    return 0;
}
