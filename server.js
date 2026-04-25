require('dotenv').config();
const express  = require('express');
const cors     = require('cors');
const helmet   = require('helmet');
const rateLimit= require('express-rate-limit');
const bcrypt   = require('bcryptjs');
const jwt      = require('jsonwebtoken');
const { OpenAI } = require('openai');
const fs   = require('fs');
const path = require('path');
const {
  Document, Packer, Paragraph, TextRun, HeadingLevel,
  Table, TableRow, TableCell, WidthType, BorderStyle,
  AlignmentType, ShadingType, PageBreak, Header, Footer,
  ImageRun,
} = require('docx');

// ── Radar chart generator — pure Node.js PNG, zero external dependencies ──
const zlib = require('zlib');
function generateRadarPNG(skills){
  // Build radar as PNG using pure Node.js pixel renderer
  const size=560, cx=280, cy=260, R=160;
  const zlib=require('zlib');
  function _crc32(buf){let c=0xFFFFFFFF,t=[];for(let i=0;i<256;i++){let x=i;for(let j=0;j<8;j++)x=(x&1)?0xEDB88320^(x>>>1):x>>>1;t[i]=x;}for(let i=0;i<buf.length;i++)c=t[(c^buf[i])&0xFF]^(c>>>8);return(c^0xFFFFFFFF)>>>0;}
  function _chunk(type,data){const l=Buffer.alloc(4);l.writeUInt32BE(data.length);const t=Buffer.from(type);const c=Buffer.alloc(4);c.writeUInt32BE(_crc32(Buffer.concat([t,data])));return Buffer.concat([l,t,data,c]);}
  function _png(w,h,px){const ihdr=Buffer.alloc(13);ihdr.writeUInt32BE(w,0);ihdr.writeUInt32BE(h,4);ihdr[8]=8;ihdr[9]=6;const rows=[];for(let y=0;y<h;y++){const r=Buffer.alloc(1+w*4);r[0]=0;for(let x=0;x<w;x++){const i=(y*w+x)*4;r[1+x*4]=px[i];r[1+x*4+1]=px[i+1];r[1+x*4+2]=px[i+2];r[1+x*4+3]=px[i+3];}rows.push(r);}const comp=zlib.deflateSync(Buffer.concat(rows),{level:6});return Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),_chunk('IHDR',ihdr),_chunk('IDAT',comp),_chunk('IEND',Buffer.alloc(0))]);}
  function _hex(h){const c=h.replace('#','');return[parseInt(c.slice(0,2),16),parseInt(c.slice(2,4),16),parseInt(c.slice(4,6),16)];}
  const pixels=new Uint8Array(size*size*4);
  function sp(x,y,r,g,b,a=255){x=Math.round(x);y=Math.round(y);if(x<0||x>=size||y<0||y>=size)return;const i=(y*size+x)*4;const af=a/255,ab=pixels[i+3]/255,ao=af+ab*(1-af);if(ao===0)return;pixels[i]=Math.round((r*af+pixels[i]*ab*(1-af))/ao);pixels[i+1]=Math.round((g*af+pixels[i+1]*ab*(1-af))/ao);pixels[i+2]=Math.round((b*af+pixels[i+2]*ab*(1-af))/ao);pixels[i+3]=Math.round(ao*255);}
  function line(x0,y0,x1,y1,r,g,b,a=255,t=1){const dx=x1-x0,dy=y1-y0,len=Math.sqrt(dx*dx+dy*dy),steps=Math.ceil(len*2);for(let i=0;i<=steps;i++){const p=i/steps,px2=x0+dx*p,py2=y0+dy*p;for(let tx=-t;tx<=t;tx++)for(let ty=-t;ty<=t;ty++)if(tx*tx+ty*ty<=t*t+1)sp(px2+tx,py2+ty,r,g,b,a);}}
  function fillPoly(pts,r,g,b,a=255){const minY=Math.max(0,Math.floor(Math.min(...pts.map(p=>p[1])))),maxY=Math.min(size-1,Math.ceil(Math.max(...pts.map(p=>p[1]))));for(let y=minY;y<=maxY;y++){const xs=[];for(let i=0;i<pts.length;i++){const[ax,ay]=pts[i],[bx2,by2]=pts[(i+1)%pts.length];if((ay<=y&&by2>y)||(by2<=y&&ay>y))xs.push(ax+(y-ay)*(bx2-ax)/(by2-ay));}xs.sort((a,b)=>a-b);for(let k=0;k<xs.length-1;k+=2)for(let x=Math.ceil(xs[k]);x<=Math.floor(xs[k+1]);x++)sp(x,y,r,g,b,a);}}
  function fillCirc(cx2,cy2,rad,r,g,b,a=255){for(let y=Math.round(cy2-rad);y<=Math.round(cy2+rad);y++)for(let x=Math.round(cx2-rad);x<=Math.round(cx2+rad);x++)if((x-cx2)**2+(y-cy2)**2<=rad**2)sp(x,y,r,g,b,a);}
  // 5x7 pixel font — digits and basic chars
  // ── Full A-Z pixel font (3x5) ──
  const GLYPHS={
    'A':[[0,1,0],[1,0,1],[1,1,1],[1,0,1],[1,0,1]],
    'B':[[1,1,0],[1,0,1],[1,1,0],[1,0,1],[1,1,0]],
    'C':[[0,1,1],[1,0,0],[1,0,0],[1,0,0],[0,1,1]],
    'D':[[1,1,0],[1,0,1],[1,0,1],[1,0,1],[1,1,0]],
    'E':[[1,1,1],[1,0,0],[1,1,0],[1,0,0],[1,1,1]],
    'F':[[1,1,1],[1,0,0],[1,1,0],[1,0,0],[1,0,0]],
    'G':[[0,1,1],[1,0,0],[1,0,1],[1,0,1],[0,1,1]],
    'H':[[1,0,1],[1,0,1],[1,1,1],[1,0,1],[1,0,1]],
    'I':[[1,1,1],[0,1,0],[0,1,0],[0,1,0],[1,1,1]],
    'J':[[0,0,1],[0,0,1],[0,0,1],[1,0,1],[0,1,0]],
    'K':[[1,0,1],[1,0,1],[1,1,0],[1,0,1],[1,0,1]],
    'L':[[1,0,0],[1,0,0],[1,0,0],[1,0,0],[1,1,1]],
    'M':[[1,0,1],[1,1,1],[1,0,1],[1,0,1],[1,0,1]],
    'N':[[1,0,1],[1,1,1],[1,1,1],[1,0,1],[1,0,1]],
    'O':[[0,1,0],[1,0,1],[1,0,1],[1,0,1],[0,1,0]],
    'P':[[1,1,0],[1,0,1],[1,1,0],[1,0,0],[1,0,0]],
    'Q':[[0,1,0],[1,0,1],[1,0,1],[1,1,1],[0,1,1]],
    'R':[[1,1,0],[1,0,1],[1,1,0],[1,0,1],[1,0,1]],
    'S':[[0,1,1],[1,0,0],[0,1,0],[0,0,1],[1,1,0]],
    'T':[[1,1,1],[0,1,0],[0,1,0],[0,1,0],[0,1,0]],
    'U':[[1,0,1],[1,0,1],[1,0,1],[1,0,1],[0,1,1]],
    'V':[[1,0,1],[1,0,1],[1,0,1],[0,1,0],[0,1,0]],
    'W':[[1,0,1],[1,0,1],[1,0,1],[1,1,1],[1,0,1]],
    'X':[[1,0,1],[1,0,1],[0,1,0],[1,0,1],[1,0,1]],
    'Y':[[1,0,1],[1,0,1],[0,1,0],[0,1,0],[0,1,0]],
    'Z':[[1,1,1],[0,0,1],[0,1,0],[1,0,0],[1,1,1]],
    '0':[[0,1,0],[1,0,1],[1,0,1],[1,0,1],[0,1,0]],
    '1':[[0,1,0],[1,1,0],[0,1,0],[0,1,0],[1,1,1]],
    '2':[[1,1,0],[0,0,1],[0,1,0],[1,0,0],[1,1,1]],
    '3':[[1,1,0],[0,0,1],[0,1,0],[0,0,1],[1,1,0]],
    '4':[[1,0,1],[1,0,1],[1,1,1],[0,0,1],[0,0,1]],
    '5':[[1,1,1],[1,0,0],[1,1,0],[0,0,1],[1,1,0]],
    '6':[[0,1,1],[1,0,0],[1,1,0],[1,0,1],[0,1,0]],
    '7':[[1,1,1],[0,0,1],[0,1,0],[0,1,0],[0,1,0]],
    '8':[[0,1,0],[1,0,1],[0,1,0],[1,0,1],[0,1,0]],
    '9':[[0,1,0],[1,0,1],[0,1,1],[0,0,1],[0,1,0]],
    '%':[[1,0,0],[0,0,1],[0,1,0],[1,0,0],[0,1,1]],
    ' ':[[0,0,0],[0,0,0],[0,0,0],[0,0,0],[0,0,0]],
    '/':[[0,0,1],[0,0,1],[0,1,0],[1,0,0],[1,0,0]],
  };
  function drawText(text,ox,oy,r,g,b,scale=1){
    let xoff=0;
    for(const ch of text.toUpperCase()){
      const gl=GLYPHS[ch]||GLYPHS[' '];
      for(let row=0;row<5;row++)
        for(let col=0;col<3;col++)
          if(gl[row][col])
            for(let sy=0;sy<scale;sy++)
              for(let sx=0;sx<scale;sx++)
                sp(ox+xoff+col*scale+sx,oy+row*scale+sy,r,g,b,240);
      xoff+=(3+1)*scale;
    }
  }
  function textWidth(t,scale=1){return t.length*(3+1)*scale;}

  function ang(i){return(Math.PI*2*i/skills.length)-Math.PI/2;}

  // Background
  const[br,bg2,bb]=_hex('#07111F');for(let i=0;i<size*size;i++){pixels[i*4]=br;pixels[i*4+1]=bg2;pixels[i*4+2]=bb;pixels[i*4+3]=255;}
  // Grid rings
  const[gr,gg,gb]=_hex('#1E3A5F');
  [0.25,0.5,0.75,1.0].forEach(v=>{const pts=skills.map((_,i)=>[cx+R*v*Math.cos(ang(i)),cy+R*v*Math.sin(ang(i))]);for(let j=0;j<pts.length;j++)line(...pts[j],...pts[(j+1)%pts.length],gr,gg,gb,v===1?100:60,1);});
  // Axis lines
  skills.forEach((_,i)=>line(cx,cy,cx+R*Math.cos(ang(i)),cy+R*Math.sin(ang(i)),gr,gg,gb,80,1));
  // Data fill + outline
  const dp=skills.map((s,i)=>[cx+R*(s.score/100)*Math.cos(ang(i)),cy+R*(s.score/100)*Math.sin(ang(i))]);
  fillPoly(dp,0,180,220,40);
  const[cr2,cg2,cb2]=_hex('#00CFEF');
  for(let j=0;j<dp.length;j++)line(...dp[j],...dp[(j+1)%dp.length],cr2,cg2,cb2,220,2);
  // Data point dots on the polygon vertices only (no label dots)
  dp.forEach(([px2,py2],i)=>{
    const s=skills[i];
    const[dr,dg,db]=s.score>=70?_hex('#00D166'):s.score>=50?_hex('#F0A500'):_hex('#E53030');
    fillCirc(px2,py2,9,dr,dg,db);
    fillCirc(px2,py2,4,15,20,30,200);
  });

  // ── SKILL LABELS: full name + score + PASS/FAIL — NO dots ──
  skills.forEach((s,i)=>{
    const a=ang(i);
    const dist=R+28;
    const lx=cx+dist*Math.cos(a), ly=cy+dist*Math.sin(a);
    const col=s.score>=70?_hex('#00D166'):s.score>=50?_hex('#F0A500'):_hex('#E53030');
    const scale=2;

    // Split long names across two lines
    const words=s.label.split(' ');
    let line1=words[0], line2=words.slice(1).join(' ');
    const scoreLine=s.score+'% '+(s.score>=70?'PASS':'FAIL');

    const w1=textWidth(line1,scale);
    const w2=line2?textWidth(line2,scale):0;
    const w3=textWidth(scoreLine,scale);
    const maxW=Math.max(w1,w2,w3);
    const totalH=line2?5*scale*3+6:5*scale*2+4; // 2 or 3 text rows

    // Position based on quadrant
    const ang_deg=(a*180/Math.PI+360)%360;
    let tx,ty;
    if(ang_deg<45||ang_deg>=315){      // TOP
      tx=lx-maxW/2; ty=ly-totalH-4;
    } else if(ang_deg<135){             // RIGHT
      tx=lx+14; ty=ly-totalH/2;
    } else if(ang_deg<225){             // BOTTOM
      tx=lx-maxW/2; ty=ly+8;
    } else {                            // LEFT
      tx=lx-maxW-14; ty=ly-totalH/2;
    }

    tx=Math.max(4,Math.min(size-maxW-4,Math.round(tx)));
    ty=Math.max(4,Math.min(size-totalH-4,Math.round(ty)));

    const[wr,wg,wb]=_hex('#E8F4FF'); // white-ish for skill name
    let yOff=0;
    drawText(line1,tx,ty+yOff,wr,wg,wb,scale); yOff+=5*scale+3;
    if(line2){ drawText(line2,tx,ty+yOff,wr,wg,wb,scale); yOff+=5*scale+3; }
    drawText(scoreLine,tx,ty+yOff,col[0],col[1],col[2],scale);
  });

  // ── LEGEND: colour key at bottom ──
  const legendItems=[
    {label:'PASS  >= 70%',col:'#00D166'},
    {label:'DEVELOPING  50-69%',col:'#F0A500'},
    {label:'FAIL  < 50%',col:'#E53030'},
  ];
  const legY=size-28, legScale=1;
  let legX=8;
  legendItems.forEach(item=>{
    const[lr,lg,lb]=_hex(item.col);
    // Small filled square instead of dot
    for(let sy=0;sy<6;sy++) for(let sx=0;sx<6;sx++) sp(legX+sx,legY+sy,lr,lg,lb,220);
    drawText(item.label,legX+9,legY,190,210,230,legScale);
    legX+=textWidth(item.label,legScale)+18;
  });

  return _png(size,size,pixels);
}

// ─────────────────────────────────────────────
// ENVIRONMENT VALIDATION — fail fast if missing
// ─────────────────────────────────────────────
const REQUIRED_ENV = ['OPENAI_API_KEY', 'JWT_SECRET', 'ADMIN_PASSWORD_HASH'];
for (const key of REQUIRED_ENV) {
  if (!process.env[key]) {
    console.error(`[FATAL] Missing required env var: ${key}`);
    console.error('Run: node generate-secrets.js  to create your .env entries');
    process.exit(1);
  }
}

const app = express();

// ─────────────────────────────────────────────
// A05 — SECURITY HEADERS (Helmet)
// ─────────────────────────────────────────────
app.use(helmet({
  contentSecurityPolicy: false, // Single-page app with inline handlers — CSP managed at nginx level in production
  crossOriginEmbedderPolicy: false,
}));

// ─────────────────────────────────────────────
// A01 — RESTRICT CORS to same origin only
// ─────────────────────────────────────────────
const ALLOWED_ORIGINS = (process.env.ALLOWED_ORIGINS || 'http://localhost:3000')
  .split(',').map(o => o.trim());

app.use(cors({
  origin: (origin, cb) => {
    // Allow requests with no origin (same-origin, curl) or whitelisted origins
    if (!origin || ALLOWED_ORIGINS.includes(origin)) return cb(null, true);
    cb(new Error(`CORS blocked: ${origin}`));
  },
  credentials: true,
}));

app.use(express.json({ limit: '4mb' })); // A03 — cap request body size (4mb allows playbook PDF base64)

// ─────────────────────────────────────────────
// A05 — SERVE STATIC FILES FROM /public ONLY
// Never serve __dirname (exposes .env, db.json, server.js)
// ─────────────────────────────────────────────
const PUBLIC_DIR = path.join(__dirname, 'public');
if (!fs.existsSync(PUBLIC_DIR)) fs.mkdirSync(PUBLIC_DIR, { recursive: true });
app.use(express.static(PUBLIC_DIR));

// ─────────────────────────────────────────────
// A09 — STRUCTURED ACCESS LOGGING
// ─────────────────────────────────────────────
const LOG_FILE = path.join(__dirname, 'access.log');
app.use((req, res, next) => {
  const start = Date.now();
  res.on('finish', () => {
    const entry = JSON.stringify({
      ts:     new Date().toISOString(),
      method: req.method,
      path:   req.path,
      status: res.statusCode,
      ip:     req.ip,
      ms:     Date.now() - start,
    });
    fs.appendFile(LOG_FILE, entry + '\n', () => {});
  });
  next();
});

// ─────────────────────────────────────────────
// A04 — RATE LIMITING
// ─────────────────────────────────────────────
const loginLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15 minutes
  max: 10,                   // max 10 login attempts per window
  message: { error: 'Too many login attempts. Try again in 15 minutes.' },
  standardHeaders: true,
  legacyHeaders: false,
});

const apiLimiter = rateLimit({
  windowMs: 60 * 1000,       // 1 minute
  max: 60,                   // 60 requests per minute
  message: { error: 'Rate limit exceeded. Slow down.' },
});

const aiLimiter = rateLimit({
  windowMs: 60 * 1000,
  max: 10,                   // max 10 AI calls per minute — protect OpenAI spend
  message: { error: 'AI rate limit reached. Wait a moment.' },
});

app.use('/api/', apiLimiter);
app.use('/api/login', loginLimiter);
app.use('/api/generate-conclusion', aiLimiter);
app.use('/api/generate-scenario', aiLimiter);
app.use('/api/grade-response', aiLimiter);

// ─────────────────────────────────────────────
// A07 — SERVER-SIDE AUTH with JWT
// ─────────────────────────────────────────────
const JWT_SECRET  = process.env.JWT_SECRET;
const JWT_EXPIRES = '8h'; // sessions expire after 8 hours

function requireAuth(req, res, next) {
  const header = req.headers.authorization;
  if (!header || !header.startsWith('Bearer ')) {
    return res.status(401).json({ error: 'Unauthorised — no token provided' });
  }
  const token = header.slice(7);
  try {
    const payload = jwt.verify(token, JWT_SECRET);
    req.user = payload;
    next();
  } catch (err) {
    return res.status(401).json({ error: 'Unauthorised — invalid or expired token' });
  }
}

// ─────────────────────────────────────────────
// A07 — LOGIN ENDPOINT (server-side, bcrypt)
// ─────────────────────────────────────────────
app.post('/api/login', loginLimiter, async (req, res) => {
  try {
    const { username, password } = req.body;
    if (!username || !password) {
      return res.status(400).json({ error: 'Username and password required' });
    }
    // Only 'admin' account supported (add more via env vars when needed)
    if (username !== 'admin') {
      // Constant-time fake comparison to prevent username enumeration
      await bcrypt.compare(password, '$2a$12$fakehashtopreventtiming000000000000000000000');
      return res.status(401).json({ error: 'Invalid credentials' });
    }
    const valid = await bcrypt.compare(password, process.env.ADMIN_PASSWORD_HASH);
    if (!valid) {
      return res.status(401).json({ error: 'Invalid credentials' });
    }
    const token = jwt.sign(
      { username: 'admin', role: 'ADMIN' },
      JWT_SECRET,
      { expiresIn: JWT_EXPIRES }
    );
    res.json({ token, role: 'ADMIN', expiresIn: JWT_EXPIRES });
  } catch (err) {
    console.error('Login error:', err.message);
    res.status(500).json({ error: 'Login failed' });
  }
});

// ─────────────────────────────────────────────
// A03 — INPUT SANITISATION HELPERS
// ─────────────────────────────────────────────
function sanitiseString(val, maxLen = 500) {
  if (typeof val !== 'string') return '';
  return val.slice(0, maxLen).replace(/[<>]/g, ''); // strip angle brackets
}

function sanitiseNumber(val, fallback = 0) {
  const n = Number(val);
  return isFinite(n) ? n : fallback;
}

// ─────────────────────────────────────────────
// DB FILE HELPERS
// ─────────────────────────────────────────────
const DB_FILE = path.join(__dirname, 'db.json');

function readDB() {
  try {
    if (!fs.existsSync(DB_FILE)) return {};
    const raw = fs.readFileSync(DB_FILE, 'utf-8');
    const parsed = JSON.parse(raw);
    // A08 — basic schema validation
    if (typeof parsed !== 'object' || Array.isArray(parsed)) throw new Error('Invalid db format');
    return parsed;
  } catch (err) {
    console.error('DB read error:', err.message);
    return {};
  }
}

function writeDB(data) {
  // A08 — validate before writing
  if (typeof data !== 'object' || Array.isArray(data)) throw new Error('Invalid data shape');
  fs.writeFileSync(DB_FILE, JSON.stringify(data, null, 2), 'utf-8');
}


// ─────────────────────────────────────────────
// DATA ENDPOINTS — protected by requireAuth
// ─────────────────────────────────────────────
app.get('/api/data', requireAuth, (req, res) => {
  try {
    res.json(readDB());
  } catch (err) {
    console.error('Load error:', err.message);
    res.status(500).json({ error: 'Failed to load data' });
  }
});

app.post('/api/data', requireAuth, (req, res) => {
  try {
    writeDB(req.body);
    res.json({ ok: true });
  } catch (err) {
    console.error('Save error:', err.message);
    res.status(500).json({ error: 'Failed to save data' });
  }
});

// ─────────────────────────────────────────────
// OPENAI CLIENT
// ─────────────────────────────────────────────
const openai = new OpenAI({ apiKey: process.env.OPENAI_API_KEY });

// ─────────────────────────────────────────────
// HELPERS — report generation
// ─────────────────────────────────────────────
function getGrade(pct) {
  if (pct >= 90) return { letter: 'A', label: 'Excellent' };
  if (pct >= 70) return { letter: 'B', label: 'Competent' };
  if (pct >= 50) return { letter: 'C', label: 'Developing' };
  return { letter: 'D', label: 'Critical Risk' };
}
function getResiliencePosture(pct) {
  if (pct >= 90) return 'HIGH — Strong incident response maturity.';
  if (pct >= 70) return 'MODERATE — Foundational capability with material gaps.';
  if (pct >= 50) return 'LOW-MODERATE — Would struggle to contain a real incident.';
  return 'CRITICAL — Unprepared to respond to a live cyber incident.';
}
function formatTime(seconds) {
  const m = Math.floor(seconds / 60), s = seconds % 60;
  return `${m}m ${s}s`;
}
function buildDecisionBreakdown(decisionHistory) {
  return decisionHistory.map((d, i) => [
    `[Decision ${i+1}] Domain: ${sanitiseString(d.skillTested||'GENERAL',50).toUpperCase()}`,
    `  Q: ${sanitiseString(d.question,300)}`,
    `  Chosen: "${sanitiseString(d.chosen,300)}"`,
    `  Result: ${d.correct?'CORRECT':'INCORRECT'}`,
    `  ${d.correct?'Why correct':'What went wrong'}: ${sanitiseString(d.feedback,400)}`,
  ].join('\n')).join('\n\n');
}
function buildSkillAnalysis(skillScores) {
  if (!skillScores) return 'Not available';
  const LABELS = {technical:'Technical Response',communication:'Communication',decision:'Decision Making',leadership:'Leadership',compliance:'Compliance',coordination:'Coordination'};
  return Object.entries(skillScores)
    .sort((a,b)=>a[1]-b[1])
    .map(([k,v])=>`  - ${LABELS[k]||k}: ${sanitiseNumber(v)}% [${v>=70?'PASS':v>=50?'BORDERLINE':'FAIL'}]`)
    .join('\n');
}

const SYSTEM_PROMPT = `You are Dr. Marcus Reid, a Senior Cybersecurity Resilience Consultant. Write precise, professional executive debrief reports for corporate clients. Be evidence-based, direct, and grounded in real cybersecurity standards. Use ONLY plain text and basic HTML: <strong>, <br>, <ul>, <li>. No markdown. No # headers.`.trim();

// ─────────────────────────────────────────────
// AI CONCLUSION — protected + rate limited
// ─────────────────────────────────────────────
app.post('/api/generate-conclusion', requireAuth, aiLimiter, async (req, res) => {
  try {
    const {
      score, maxScore, scenarioTitle, level, clientName,
      decisionHistory, skillScores, timeTaken,
    } = req.body;

    // A03 — validate and sanitise all inputs
    if (!Array.isArray(decisionHistory) || decisionHistory.length === 0) {
      return res.status(400).json({ error: 'decisionHistory must be a non-empty array' });
    }
    if (decisionHistory.length > 50) {
      return res.status(400).json({ error: 'Too many decisions' });
    }

    const safeScore    = sanitiseNumber(score);
    const safeMax      = sanitiseNumber(maxScore, 100);
    const safeTitle    = sanitiseString(scenarioTitle, 200);
    const safeClient   = sanitiseString(clientName, 200);
    const safeLevel    = ['management','working'].includes(level) ? level : 'management';
    const safeTime     = sanitiseNumber(timeTaken);

    const pct          = Math.round((safeScore / safeMax) * 100);
    const grade        = getGrade(pct);
    const posture      = getResiliencePosture(pct);
    const correctCount = decisionHistory.filter(d => d.correct === true).length;
    const incorrectCount = decisionHistory.length - correctCount;
    const weakSkills   = skillScores ? Object.entries(skillScores).filter(([_,v])=>v<70).map(([k])=>k) : [];
    const critSkills   = skillScores ? Object.entries(skillScores).filter(([_,v])=>v<50).map(([k])=>k) : [];
    const avgTime      = safeTime / decisionHistory.length;
    const timeComment  = avgTime < 15 ? 'Under 15s avg — possible overconfidence.'
                       : avgTime > 90 ? 'Over 90s avg — hesitation in a live incident would cost containment time.'
                       : 'Decision pacing within acceptable range.';

    const userPrompt = `
SIMULATION RECORD
Client: ${safeClient || 'Confidential'}
Scenario: ${safeTitle}
Level: ${safeLevel === 'management' ? 'Management & Leadership (C-Suite, Directors, VPs)' : 'Working Level (SOC Analysts, IT Engineers)'}
Date: ${new Date().toLocaleDateString('en-GB')}

IMPORTANT CONTEXT:
${safeLevel === 'management'
  ? 'This is a MANAGEMENT LEVEL simulation. Participants are senior leaders, not technical staff. Do NOT assess or criticise Technical Response skills — management are not expected to perform hands-on technical containment. Their role is leadership, communication, compliance, decision-making, and coordination. If Technical Response shows 0%, note that this skill is NOT applicable for management participants.'
  : 'This is a WORKING LEVEL simulation. Participants are SOC analysts and IT engineers. Technical response is the primary expected skill.'}

PERFORMANCE
Score: ${safeScore}/${safeMax} (${pct}%) — Grade: ${grade.letter} ${grade.label}
Correct: ${correctCount}/${decisionHistory.length} | Incorrect: ${incorrectCount}/${decisionHistory.length}
Time: ${formatTime(safeTime)} | Avg per decision: ${Math.round(avgTime)}s — ${timeComment}
Posture: ${posture}

SKILL SCORES
${buildSkillAnalysis(skillScores)}
${weakSkills.length ? `Below threshold: ${weakSkills.join(', ')}` : 'All skills passed.'}
${critSkills.length ? `Critical failures: ${critSkills.join(', ')}` : ''}

DECISIONS
${buildDecisionBreakdown(decisionHistory)}

IMPORTANT FREE-TEXT AND PARTICIPANT ANALYSIS RULES:
- If free-text responses are present, analyse them directly and prioritise them over MCQ-only correctness.
- Use AI response scores, missing actions, expected actions, and typed answer quality to identify gaps in reasoning.
- Mention recurring weaknesses by participant and team when the data contains participantName or team.
- Identify who needs improvement and in which skill domain when enough data is available.

Write the full executive debrief using ONLY these HTML tags: <strong>, <br>, <ul>, <li>. No markdown. No other tags.

Use EXACTLY these 7 section headings — each must be wrapped in <strong>Title</strong><br> on its own line:

<strong>Executive Summary</strong><br>
[3 sentences: what was tested, overall result, key finding]

<strong>Cyber Resilience Posture Assessment</strong><br>
[3-4 sentences on practical resilience posture]

<strong>Skill Domain Performance</strong><br>
[For each skill tested, write: SkillName: XX% [PASS/FAIL] — one sentence observation. Skip Technical Response entirely if this is management level.]

<strong>Decision Failures & Consequences</strong><br>
[List only incorrect decisions with <ul><li> items. If none, state that clearly.]

<strong>Correct Responses</strong><br>
[List correct decisions with <ul><li> items. Be specific.]

<strong>Prioritised Recommendations</strong><br>
[Exactly 3 <ul><li> items. Start each with [IMMEDIATE], [30 DAYS], or [NEXT QUARTER] followed by the recommendation.]

<strong>Consultant's Verdict</strong><br>
[2 sentences only: overall verdict and single most important next action.]
`.trim();

    const completion = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      messages: [
        { role: 'system', content: SYSTEM_PROMPT },
        { role: 'user',   content: userPrompt },
      ],
      temperature: 0.25,
      max_tokens: 1600,
    });

    res.json({ conclusion: completion.choices[0].message.content });

  } catch (err) {
    console.error('AI error:', err.message);
    console.error('AI error status:', err.status);
    console.error('AI error type:', err.constructor?.name);
    const clientMsg = err.status === 401 ? 'Invalid OpenAI API key — check your .env file'
                    : err.status === 429 ? 'OpenAI rate limit or quota exceeded'
                    : err.status === 404 ? 'OpenAI model not found — check model name'
                    : 'Failed to generate report';
    res.status(500).json({ error: clientMsg });
  }
});

// ─────────────────────────────────────────────
// AI SCENARIO GENERATOR — protected
// ─────────────────────────────────────────────
app.post('/api/generate-scenario', requireAuth, aiLimiter, async (req, res) => {
  try {
    const prompt       = sanitiseString(req.body.prompt || '', 800);
    const numDecisions = Math.min(20, Math.max(1, parseInt(req.body.numDecisions) || 4));
    const level        = ['Both','Management','Working'].includes(req.body.level) ? req.body.level : 'Both';
    const alertDetail  = ['standard','detailed','realistic'].includes(req.body.alertDetail) ? req.body.alertDetail : 'detailed';
    const sourceMode   = req.body.sourceMode === 'playbook' ? 'playbook' : 'brief';
    const rawPlaybook  = typeof req.body.playbookText === 'string' ? req.body.playbookText : '';
    if (!prompt) return res.status(400).json({ error: 'Prompt is required' });

    // ── Extract playbook text from PDF/DOCX base64 if needed ──
    let playbookText = '';
    if(sourceMode === 'playbook' && rawPlaybook){
      if(rawPlaybook.startsWith('__PDF_B64__:')){
        // Use OpenAI vision to extract text from PDF pages
        try {
          const pdfB64 = rawPlaybook.slice('__PDF_B64__:'.length);
          const extractRes = await openai.chat.completions.create({
            model: 'gpt-4o',
            max_tokens: 4000,
            messages:[{
              role:'user',
              content:[
                { type:'text', text:'Extract all text content from this PDF document. Return only the raw text, preserving structure and headings. Do not summarise — extract everything.' },
                { type:'image_url', image_url:{ url:`data:application/pdf;base64,${pdfB64}`, detail:'high' } }
              ]
            }]
          });
          playbookText = extractRes.choices[0]?.message?.content || '';
        } catch(extractErr) {
          console.warn('PDF extraction failed, using prompt only:', extractErr.message);
          playbookText = '';
        }
      } else if(rawPlaybook.startsWith('__DOCX_B64__:')){
        // DOCX: server-side extraction using docx library
        try {
          const { extractRawText } = require('mammoth');
          const docxB64 = rawPlaybook.slice('__DOCX_B64__:'.length);
          const buf = Buffer.from(docxB64, 'base64');
          const result = await extractRawText({ buffer: buf });
          playbookText = result.value || '';
        } catch(docxErr){
          console.warn('DOCX extraction failed:', docxErr.message);
          playbookText = '';
        }
      } else {
        // Plain text — use directly, cap at 12000 chars
        playbookText = rawPlaybook.slice(0, 12000);
      }
    }

    const levelNote = level === 'Management'
      ? 'Decisions should focus on leadership, communication, compliance and executive judgment — not deep technical actions.'
      : level === 'Working'
      ? 'Decisions should focus on technical response, forensics, containment and SOC/IT actions — not executive communications.'
      : 'Mix decisions across both management (leadership, comms, compliance) and working level (technical, forensics, containment).';

    // Build playbook injection block
    const playbookBlock = playbookText
      ? `\n\nCLIENT PLAYBOOK / INCIDENT RESPONSE PROCEDURE:\n${'='.repeat(60)}\n${playbookText.slice(0,10000)}\n${'='.repeat(60)}\n\nPLAYBOOK USAGE RULES:\n- The scenario MUST be grounded in the steps, roles, timelines and procedures described in this playbook\n- Decision options must include: (1) the correct playbook-compliant action, and (2) common real-world deviations from the playbook as wrong answers\n- Good feedback must reference the specific playbook step or procedure that was correctly followed\n- Bad feedback must explain exactly which playbook step was skipped or violated\n- The scenario title, briefing and timeline should reflect the incident type the playbook covers\n- Objectives should map directly to the playbook\'s stated goals`
      : '';

    const systemPrompt = `You are an expert cybersecurity training scenario designer for NexaCyberSim.
Generate a complete, realistic cyber crisis simulation scenario as a single JSON object.${playbookBlock}

The JSON must strictly follow this schema:
{
  "title": "string — concise, dramatic incident title",
  "desc": "string — 1-2 sentence summary for the scenario card",
  "icon": "string — single relevant emoji",
  "severity": "CRITICAL" | "HIGH" | "MEDIUM" | "LOW",
  "duration": "15 min" | "20 min" | "30 min",
  "level": "${level}",
  "teams": ["array of 2-5 team/department names involved"],
  "skills": ["array of 2-4 values from: technical, communication, decision, leadership, compliance, coordination"],
  "overview": "string — 3-5 sentence situation overview describing the incident context",
  "objectives": "string — 2-4 bullet points of what participants must achieve (plain text, use newlines)",
  "timeline": [
    { "time": "HH:MM", "badge": "r"|"a"|"b", "label": "string", "text": "string — event description" }
  ],
  "introSlides": [
    { "title": "string", "content": "string — 2-4 paragraphs of context/evidence" }
  ],
  "decisions": [
    {
      "alertType": "cr"|"wa"|"in",
      "alertLabel": "string — e.g. INCIDENT UPDATE",
      "alertText": "string — see alert text rules below",
      "question": "string — the specific decision question the participant must answer",
      "expectedActions": "string — semicolon-separated ideal free-text response actions, e.g. isolate affected systems; preserve logs; notify IR lead; escalate to CISO",
      "timeLimit": 60,
      "decTeams": ["team names involved in this decision"],
      "skillTested": "technical"|"communication"|"decision"|"leadership"|"compliance"|"coordination",
      "options": [
        { "text": "string — option text", "correct": true|false }
      ],
      "goodFeedback": "string — explanation for the correct choice",
      "badFeedback": "string — explanation for wrong choices"
    }
  ]
}

Rules:
- Generate EXACTLY ${numDecisions} decisions — no more, no less
- Each decision must have exactly 4 options, exactly 1 marked correct:true
- The "question" field is REQUIRED and must be a clear, specific question the participant must answer
- Every decision MUST include "expectedActions"
- "expectedActions" must describe the ideal typed/tabletop response as semicolon-separated actions
- If a playbook is provided, expectedActions must be derived from the playbook where possible
- badge: "r"=red/critical, "a"=amber/warning, "b"=blue/info
- alertType: "cr"=critical/red alert, "wa"=warning/amber alert, "in"=info/blue alert
- timeline must have 4-6 events spanning the incident progression
- intro slides: 1-2 slides maximum
- Participant level focus: ${levelNote}
- Make the scenario realistic, industry-specific, technically accurate
- If the scenario involves dark web, data leak, or public exposure: decisions must cover the full crisis arc — discovery of the leak, dark web monitoring alert, media/social media pressure, customer notification, regulatory response, and reputation management. Include realistic dark web forum names (e.g. BreachForums, RaidForums successor, Telegram channels), threat actor names, data sample descriptions, and price/buyer details where relevant. Make it feel like a genuine public crisis unfolding in real time.
- If the scenario involves double extortion ransomware: include a decision point where the threat actor publishes a sample of stolen data on their leak site (e.g. "LockBit Blog", "ALPHV/BlackCat leak site") as proof, and the organisation must decide how to respond publicly while negotiating or refusing payment.
- If the scenario involves third-party/vendor breach: the organisation discovers their data was leaked via a supplier — include decisions around notifying customers before full scope is known, managing supplier relationship, and regulatory obligations when the breach is not directly your fault.

ALERT TEXT RULES (alertText field) — detail level: ${alertDetail}
IMPORTANT: Do NOT write short, vague alert texts. Each alertText must feel like a real incident feed entry that puts the participant under genuine pressure.
${alertDetail === 'standard'
  ? `- Write alertText as 3-5 sentences. Include: what happened, which systems or data are affected, and current status. Use <strong> for key facts. Never write only 1-2 sentences — always give enough context for a meaningful decision.`
  : alertDetail === 'detailed'
  ? `- Write alertText as a rich incident update of 6-10 sentences minimum. You MUST include: (1) what has happened with specific details, (2) exact systems/accounts/data involved, (3) timestamp or timeframe, (4) current impact and spread status, (5) what is still unknown or under investigation. Use <strong> tags for critical values. Use <code> tags for hostnames, IPs, file paths, account names. Make each decision feel like reading a real escalation message from your SOC or IT team. Never write a vague one-liner.`
  : `- Write alertText as a hyper-realistic SIEM/SOC/NOC alert. MANDATORY content: precise timestamps (e.g. 09:14:32 UTC), real-looking IP addresses (e.g. 185.220.101.47), hostnames (e.g. CORP-WS-042), account names (e.g. j.smith@company.com), file paths (e.g. C:\\Users\\jsmith\\AppData), Windows Event IDs where relevant, affected asset counts, severity level indicator. Format technical details in <code> blocks. Use <strong> for the most critical values. Write 8-15 lines of content minimum. Model it on real alerts from Microsoft Sentinel, Splunk, CrowdStrike Falcon, or Darktrace. The participant must feel they are genuinely responding to a live incident.`
}
- Return ONLY the JSON object, no markdown fences, no explanation`;

    const completion = await openai.chat.completions.create({
      model: 'gpt-4o',
      max_tokens: Math.max(playbookText ? 5000 : 4000, numDecisions * (alertDetail === 'realistic' ? 1000 : alertDetail === 'detailed' ? 750 : 550)),
      temperature: 0.8,
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: `Generate a cyber crisis simulation scenario based on this brief: ${prompt}` },
      ],
    });

    const raw = completion.choices[0]?.message?.content || '';
    // Strip any accidental markdown fences
    const cleaned = raw.replace(/^```(?:json)?\s*/i, '').replace(/\s*```$/i, '').trim();
    let scenario;
    try {
      scenario = JSON.parse(cleaned);
    } catch (parseErr) {
      console.error('JSON parse failed:', parseErr.message, '\nRaw:', raw.slice(0, 300));
      return res.status(500).json({ error: 'AI returned invalid JSON. Try again.' });
    }

    // Basic validation
    if (!scenario.title || !scenario.decisions || !Array.isArray(scenario.decisions)) {
      return res.status(500).json({ error: 'AI scenario missing required fields. Try again.' });
    }

    res.json({ scenario });
  } catch (err) {
    console.error('Generate scenario error:', err.message);
    const clientMsg = err.status === 429 ? 'OpenAI rate limit exceeded — try again shortly'
                    : err.status === 401 ? 'Invalid OpenAI API key'
                    : 'Failed to generate scenario';
    res.status(500).json({ error: clientMsg });
  }
});

// ─────────────────────────────────────────────
// WORD EXPORT — protected
// ─────────────────────────────────────────────
app.post('/api/export-word', requireAuth, async (req, res) => {
  try {
    const {
      clientName, scenarioTitle, level, score, maxScore, pct, grade,
      date, correctCount, totalDecisions, aiConclusion, skills, decisions, frameworks,
    } = req.body;

    const NAVY='002147',ACCENT='005B9A',SILVER='E8EDF2',WHITE_='FFFFFF',
          DARK='1A1A2E',MID='4A5568',LIGHT='718096',
          G_GREEN='1B6B3A',G_RED='B91C1C',G_AMBER='92400E',G_BLUE='1E40AF';
    const gradeColor=grade==='A'?G_GREEN:grade==='B'?G_BLUE:grade==='C'?G_AMBER:G_RED;

    function stripHtml(h){return(h||'').replace(/<strong>/gi,'').replace(/<\/strong>/gi,'').replace(/<br\s*\/?>/gi,'\n').replace(/<li>/gi,'• ').replace(/<\/li>/gi,'\n').replace(/<[^>]+>/g,'').trim();}
    function noB(){return{top:{style:BorderStyle.NONE},bottom:{style:BorderStyle.NONE},left:{style:BorderStyle.NONE},right:{style:BorderStyle.NONE}};}
    function secHead(text,topSpace=320){return new Paragraph({children:[new TextRun({text:text.toUpperCase(),bold:true,size:22,color:WHITE_,font:'Calibri'})],spacing:{before:topSpace,after:0},shading:{type:ShadingType.CLEAR,fill:ACCENT},border:{left:{color:NAVY,size:24,style:BorderStyle.SINGLE}},indent:{left:120}});}
    function bPara(text,opts={}){return new Paragraph({children:[new TextRun({text:text||'',size:opts.size||20,color:opts.color||DARK,bold:opts.bold||false,italics:opts.italic||false,font:'Calibri'})],spacing:{after:opts.after||80},indent:opts.indent?{left:240}:{}});}
    function bBullet(text,color){return new Paragraph({children:[new TextRun({text:text||'',size:20,color:color||DARK,font:'Calibri'})],bullet:{level:0},spacing:{after:80},indent:{left:360,hanging:260}});}
    function hRule(){return new Paragraph({border:{bottom:{color:SILVER,size:6,style:BorderStyle.SINGLE}},spacing:{before:120,after:120}});}

    function metricTable(items){
      const pairs=[];for(let i=0;i<items.length;i+=2)pairs.push([items[i],items[i+1]]);
      return new Table({rows:pairs.map(p=>new TableRow({children:p.filter(Boolean).map(item=>new TableCell({children:[new Paragraph({children:[new TextRun({text:item.val,bold:true,size:40,color:ACCENT,font:'Calibri'})],alignment:AlignmentType.CENTER}),new Paragraph({children:[new TextRun({text:item.lbl,size:16,color:LIGHT,font:'Calibri'})],alignment:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:'EEF4FB'},margins:{top:140,bottom:140,left:200,right:200},borders:noB()}))})),width:{size:100,type:WidthType.PERCENTAGE},borders:{...noB(),insideH:{style:BorderStyle.NONE},insideV:{style:BorderStyle.NONE}}});
    }

    function skillTable(skills){
      const hdr=new TableRow({children:['Skill Domain','Score','Status','Assessment'].map((h,i)=>new TableCell({children:[new Paragraph({children:[new TextRun({text:h,bold:true,size:18,color:WHITE_,font:'Calibri'})],alignment:i===0?AlignmentType.LEFT:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:NAVY},margins:{top:80,bottom:80,left:120,right:120}})),tableHeader:true});
      const rows=skills.map((sk,i)=>{
        const sc=sk.score>=70?G_GREEN:sk.score>=50?G_AMBER:G_RED;
        const asmt=sk.score>=90?'Excellent':sk.score>=70?'Competent':sk.score>=50?'Developing':'Needs Improvement';
        const bg=i%2===0?SILVER:WHITE_;
        return new TableRow({children:[
          new TableCell({children:[new Paragraph({children:[new TextRun({text:sk.label,size:18,font:'Calibri'})]})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:120,right:120}}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:`${sk.score}%`,bold:true,size:18,color:sc,font:'Calibri'})],alignment:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:120,right:120}}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:sk.pass?'PASS':'FAIL',bold:true,size:18,color:sc,font:'Calibri'})],alignment:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:120,right:120}}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:asmt,size:18,color:sc,font:'Calibri'})],alignment:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:120,right:120}}),
        ]});
      });
      return new Table({rows:[hdr,...rows],width:{size:100,type:WidthType.PERCENTAGE}});
    }

    function decisionsTable(decisions){
      const hdr=new TableRow({children:['#','Decision Question','Outcome','Key Finding'].map((h,i)=>new TableCell({children:[new Paragraph({children:[new TextRun({text:h,bold:true,size:17,color:WHITE_,font:'Calibri'})],alignment:i===0?AlignmentType.CENTER:AlignmentType.LEFT})],shading:{type:ShadingType.CLEAR,fill:NAVY},margins:{top:80,bottom:80,left:100,right:100}})),tableHeader:true});
      const rows=decisions.map((d,i)=>{
        const oc=d.correct?G_GREEN:G_RED;
        const bg=i%2===0?SILVER:WHITE_;
        return new TableRow({children:[
          new TableCell({children:[new Paragraph({children:[new TextRun({text:String(d.index),size:18,bold:true,color:MID,font:'Calibri'})],alignment:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:100,right:100},width:{size:6,type:WidthType.PERCENTAGE}}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:d.question||'',size:17,color:DARK,italics:true,font:'Calibri'})]})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:100,right:100},width:{size:34,type:WidthType.PERCENTAGE}}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:d.correct?'✓ Correct':'✗ Incorrect',size:18,bold:true,color:oc,font:'Calibri'})],alignment:AlignmentType.CENTER})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:100,right:100},width:{size:14,type:WidthType.PERCENTAGE}}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:d.feedback||'',size:17,color:MID,font:'Calibri'})]})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:80,left:100,right:100},width:{size:46,type:WidthType.PERCENTAGE}}),
        ]});
      });
      return new Table({rows:[hdr,...rows],width:{size:100,type:WidthType.PERCENTAGE}});
    }

    function infoRow(label,value,shaded){
      const bg=shaded?SILVER:WHITE_,nb=noB();
      return new TableRow({children:[
        new TableCell({children:[new Paragraph({children:[new TextRun({text:label,size:16,color:LIGHT,font:'Calibri'})]})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:40,left:160,right:160},borders:nb}),
        new TableCell({children:[new Paragraph({children:[new TextRun({text:value||'',size:20,color:DARK,font:'Calibri'})]})],shading:{type:ShadingType.CLEAR,fill:bg},margins:{top:80,bottom:40,left:160,right:160},borders:nb}),
      ]});
    }

    // ── Parse AI HTML into structured Word paragraphs ──
    function parseAIConclusion(raw){
      if(!raw) return [bPara('No AI analysis available.',{color:LIGHT})];

      const SECTION_KW = [
        'Executive Summary','Cyber Resilience Posture','Skill Domain Performance',
        'Decision Failures','Decision Analysis','Correct Responses',
        'Prioritised Recommendations','Recommendations',
        "Consultant's Verdict",'Verdict','Key Findings','Overall Assessment','Overall Verdict',
      ];

      // PRE-CLEAN: decode entities, strip emojis/section labels, normalise HTML
      let cleaned = raw
        .replace(/[\u{1F000}-\u{1FFFF}\u{2600}-\u{27BF}\u{FE00}-\u{FE0F}]/gu, '')
        .replace(/SECTION\s+\d+/gi, '')
        .replace(/&amp;/gi,'&').replace(/&apos;/gi,"'").replace(/&quot;/gi,'"')
        .replace(/&lt;/gi,'<').replace(/&gt;/gi,'>')
        .replace(/<br\s*\/?>/gi, '\n')
        // Mark <strong> headings
        .replace(/<strong[^>]*>([^<]*)<\/strong>/gi, '\x01$1\x02')
        // Mark <li> bullets — handle both <li> and standalone ● bullet paragraphs
        .replace(/<li[^>]*>/gi, '\n\x03').replace(/<\/li>/gi,'')
        .replace(/<ul[^>]*>|<\/ul>/gi,'')
        .replace(/<[^>]+>/g,'')
        .replace(/[ \t]{2,}/g,' ')
        .trim();

      // Split on heading markers
      const segments = cleaned.split(/(\x01[^\x02]*\x02)/g);
      const elements = [];

      // Helper: render a skill row
      function skillRow(lbl, pct2, status, obs){
        const pctN=parseInt(pct2);
        const sc=status==='PASS'?G_GREEN:pctN>=50?G_AMBER:G_RED;
        const bg=status==='PASS'?'F0FFF4':pctN>=50?'FFFBEB':'FFF5F5';
        return new Paragraph({
          children:[
            new TextRun({text:lbl.trim(),size:18,bold:true,color:DARK,font:'Calibri'}),
            new TextRun({text:'   '+pct2+'%',size:18,bold:true,color:sc,font:'Calibri'}),
            new TextRun({text:'   '+status,size:16,bold:true,color:sc,font:'Calibri'}),
            obs?new TextRun({text:'   '+obs.trim(),size:17,color:MID,italics:true,font:'Calibri'}):new TextRun({text:''}),
          ],
          spacing:{before:60,after:60},indent:{left:200},
          shading:{type:ShadingType.CLEAR,fill:bg},
          border:{
            top:{color:SILVER,size:2,style:BorderStyle.SINGLE},
            bottom:{color:SILVER,size:2,style:BorderStyle.SINGLE},
            left:{color:sc,size:14,style:BorderStyle.SINGLE},
            right:{color:SILVER,size:2,style:BorderStyle.SINGLE},
          },
        });
      }

      // Helper: render timing badge + action
      function timingBadge(timing, action){
        const tc=timing==='IMMEDIATE'?G_RED:timing==='30 DAYS'?G_AMBER:G_BLUE;
        const bg=timing==='IMMEDIATE'?'FFF5F5':timing==='30 DAYS'?'FFFBEB':'EFF6FF';
        return [
          new Paragraph({
            children:[new TextRun({text:' '+timing+' ',bold:true,size:16,color:WHITE_,font:'Calibri'})],
            spacing:{before:160,after:0},
            shading:{type:ShadingType.CLEAR,fill:tc},
          }),
          new Paragraph({
            children:[new TextRun({text:action,size:19,color:DARK,font:'Calibri'})],
            spacing:{before:0,after:100},indent:{left:200},
            border:{left:{color:tc,size:14,style:BorderStyle.SINGLE}},
            shading:{type:ShadingType.CLEAR,fill:bg},
          }),
        ];
      }

      // Helper: render regular bullet
      function regularBullet(text){
        return new Paragraph({
          children:[
            new TextRun({text:'\u2014  ',size:19,color:ACCENT,bold:true,font:'Calibri'}),
            new TextRun({text:text,size:19,color:DARK,font:'Calibri'}),
          ],
          spacing:{before:50,after:70},indent:{left:220,hanging:220},
        });
      }

      // Helper: process a bullet text (check for timing/skill patterns)
      function processBulletText(text){
        if(!text) return null;
        // Timing badge — with or without brackets, various separators
        const tM = text.match(/^\[?(IMMEDIATE|30 DAYS|NEXT QUARTER)\]?[\s\u2014\u2013:–\-]+(.+)/i);
        if(tM) return timingBadge(tM[1].trim().toUpperCase(), tM[2].trim());
        // Timing badge without separator (AI sometimes writes "IMMEDIATE Do this...")
        const tM2 = text.match(/^(IMMEDIATE|30 DAYS|NEXT QUARTER)\s+(.+)/i);
        if(tM2) return timingBadge(tM2[1].trim().toUpperCase(), tM2[2].trim());
        // Skill row in bullet format
        const sM = text.match(/^([A-Za-z ]+?):\s*(\d+)%\s*\[([A-Z]+)\]\s*[\u2014\u2013—–\-]?\s*(.*)/);
        if(sM) return [skillRow(sM[1],sM[2],sM[3],sM[4])];
        return [regularBullet(text)];
      }

      segments.forEach(seg => {
        if(!seg||!seg.trim()) return;

        // ── Heading segment ──
        const hMatch = seg.match(/^\x01([\s\S]*?)\x02$/);
        if(hMatch){
          const title = hMatch[1].replace(/SECTION\s*\d*/gi,'').replace(/^[\s\d.:–—\-]+/,'').trim();
          if(!title) return;
          elements.push(new Paragraph({
            children:[new TextRun({text:title,bold:true,size:23,color:NAVY,font:'Calibri'})],
            spacing:{before:400,after:120},
            border:{bottom:{color:ACCENT,size:8,style:BorderStyle.SINGLE}},
          }));
          return;
        }

        // ── Content segment ──
        // Collect lines and merge standalone ● with the next line
        const rawLines = seg.split('\n').map(l=>l.trim()).filter(Boolean);
        const mergedLines = [];
        let i = 0;
        while(i < rawLines.length){
          const line = rawLines[i];
          // Standalone bullet char — merge with next line
          if((line === '\u25CF' || line === '\u2022' || line === '\u2014' || line === '-') && i+1 < rawLines.length){
            const next = rawLines[i+1].replace(/^\x03\s*/,'').trim();
            mergedLines.push('\x03' + next);
            i += 2;
          } else {
            mergedLines.push(line);
            i++;
          }
        }

        // Now process merged lines
        let j = 0;
        while(j < mergedLines.length){
          const line = mergedLines[j];
          const isBullet = line.startsWith('\x03');
          const text = line.replace(/^\x03\s*/,'').trim();
          if(!text){ j++; continue; }

          if(isBullet){
            const result = processBulletText(text);
            if(result) Array.isArray(result) ? elements.push(...result) : elements.push(result);
            j++; continue;
          }

          // Check for 3-line skill pattern: Label / XX% / PASS|FAIL
          if(j+2 < mergedLines.length){
            const l2 = mergedLines[j+1]?.replace(/^\x03\s*/,'').trim()||'';
            const l3 = mergedLines[j+2]?.replace(/^\x03\s*/,'').trim()||'';
            const pctM = l2.match(/^(\d+)%$/);
            const statM = l3.match(/^(PASS|FAIL|BORDERLINE)$/i);
            if(pctM && statM && text.length<50 && !/^\d/.test(text)){
              let obs = '';
              if(j+3 < mergedLines.length){
                const l4 = mergedLines[j+3]?.replace(/^\x03\s*/,'').trim()||'';
                if(l4.match(/^[\u2014\u2013—–\-]/) || l4.match(/^(This|The|It |Strong|Excel|Develop|Needs)/)){
                  obs = l4.replace(/^[\u2014\u2013—–\-\s]+/,'');
                  j++;
                }
              }
              elements.push(skillRow(text, pctM[1], statM[1].toUpperCase(), obs));
              j += 3; continue;
            }
          }

          // 2-line skill pattern: "Label  XX%  PASS|FAIL  observation" (all on one line from \x01 block)
          const oneLine = text.match(/^([A-Za-z ]+?)\s{2,}(\d+)%\s{2,}(PASS|FAIL)\s{2,}(.*)/);
          if(oneLine){
            elements.push(skillRow(oneLine[1], oneLine[2], oneLine[3], oneLine[4]));
            j++; continue;
          }

          // Check if untagged section heading
          const isHeading = SECTION_KW.some(k=>{
            const kl=k.toLowerCase().replace(/[''']/g,"'");
            const tl=text.toLowerCase().replace(/[''']/g,"'");
            return tl.includes(kl) && text.length < k.length+20;
          });
          if(isHeading){
            const title = text.replace(/SECTION\s*\d*/gi,'').replace(/^[\s\d.:–—\-]+/,'').trim();
            elements.push(new Paragraph({
              children:[new TextRun({text:title,bold:true,size:23,color:NAVY,font:'Calibri'})],
              spacing:{before:400,after:120},
              border:{bottom:{color:ACCENT,size:8,style:BorderStyle.SINGLE}},
            }));
            j++; continue;
          }

          // Plain prose
          if(text.trim()) elements.push(new Paragraph({
            children:[new TextRun({text:text.replace(/\s+/g,' ').trim(),size:20,color:DARK,font:'Calibri'})],
            spacing:{before:60,after:140},
            line:{value:280,rule:'auto'},
          }));
          j++;
        }
      });

      return elements.length ? elements : [bPara('No content available.',{color:LIGHT})];
    }

    const conclusionParas = parseAIConclusion(aiConclusion);

    // ── Generate radar chart PNG (pure Node.js, no external deps) ──
    const radarPNG = skills && skills.length ? generateRadarPNG(skills) : null;

    const passedCount=skills.filter(s=>s.pass).length;
    const failedCount=skills.filter(s=>!s.pass).length;
    const passNote = passedCount + ' of ' + skills.length + ' skill domains met the 70% pass threshold.' +
      (failedCount > 0 ? ' ' + failedCount + ' domain' + (failedCount>1?'s':'') + ' require' + (failedCount===1?'s':'') + ' focused remediation.' : ' All domains are performing adequately.');

    // ── Helper: coloured cover accent bar ──
    function accentBar(color){
      return new Table({
        width:{size:100,type:WidthType.PERCENTAGE},
        borders:{...noB(),insideH:{style:BorderStyle.NONE},insideV:{style:BorderStyle.NONE}},
        rows:[new TableRow({children:[
          new TableCell({children:[new Paragraph({children:[new TextRun({text:' ',size:4})]})],
            shading:{type:ShadingType.CLEAR,fill:color},
            width:{size:3,type:WidthType.PERCENTAGE},
            borders:noB()}),
          new TableCell({children:[new Paragraph({children:[new TextRun({text:' ',size:4})]})],
            shading:{type:ShadingType.CLEAR,fill:'F4F7FB'},
            width:{size:97,type:WidthType.PERCENTAGE},
            borders:noB()}),
        ]})],
      });
    }

    // ── Skill visual bar row (replaces plain text) ──
    function skillBarTable(skills){
      const rows = skills.map((sk,i)=>{
        const sc = sk.score>=70?G_GREEN:sk.score>=50?G_AMBER:G_RED;
        const scLight = sk.score>=70?'E8F5EE':sk.score>=50?'FEF3C7':'FEE2E2';
        const barFilled = Math.round(sk.score * 0.9); // max 90% width of cell
        const barEmpty  = 90 - barFilled;
        const status = sk.pass?'PASS':'FAIL';
        const asmt = sk.score>=90?'Excellent':sk.score>=70?'Competent':sk.score>=50?'Developing':'Needs Work';
        const bg = i%2===0?'F8FAFC':WHITE_;
        return new TableRow({children:[
          // Skill name
          new TableCell({
            children:[new Paragraph({children:[new TextRun({text:sk.label,size:19,bold:true,color:DARK,font:'Calibri'})],spacing:{before:60,after:60}})],
            shading:{type:ShadingType.CLEAR,fill:bg},
            margins:{top:100,bottom:100,left:160,right:120},
            width:{size:22,type:WidthType.PERCENTAGE},
            borders:{...noB(),left:{color:sc,size:18,style:BorderStyle.SINGLE}},
          }),
          // Visual progress bar cell
          new TableCell({
            children:[
              new Paragraph({spacing:{before:80,after:0},children:[new TextRun({text:' ',size:4})]}),
              new Table({
                width:{size:100,type:WidthType.PERCENTAGE},
                borders:{...noB(),insideH:{style:BorderStyle.NONE},insideV:{style:BorderStyle.NONE}},
                rows:[new TableRow({children:[
                  new TableCell({
                    children:[new Paragraph({children:[new TextRun({text:' ',size:10})]})],
                    shading:{type:ShadingType.CLEAR,fill:sc},
                    width:{size:barFilled,type:WidthType.PERCENTAGE},
                    borders:noB(),
                  }),
                  new TableCell({
                    children:[new Paragraph({children:[new TextRun({text:' ',size:10})]})],
                    shading:{type:ShadingType.CLEAR,fill:'E2E8F0'},
                    width:{size:barEmpty,type:WidthType.PERCENTAGE},
                    borders:noB(),
                  }),
                  new TableCell({
                    children:[new Paragraph({children:[new TextRun({text:' ',size:4})]})],
                    width:{size:10,type:WidthType.PERCENTAGE},
                    borders:noB(),
                  }),
                ]})],
              }),
              new Paragraph({spacing:{before:0,after:80},children:[new TextRun({text:' ',size:4})]}),
            ],
            shading:{type:ShadingType.CLEAR,fill:bg},
            margins:{top:80,bottom:80,left:80,right:80},
            width:{size:44,type:WidthType.PERCENTAGE},
            borders:noB(),
          }),
          // Score %
          new TableCell({
            children:[new Paragraph({children:[new TextRun({text:`${sk.score}%`,bold:true,size:22,color:sc,font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:60,after:60}})],
            shading:{type:ShadingType.CLEAR,fill:bg},
            margins:{top:100,bottom:100,left:80,right:80},
            width:{size:10,type:WidthType.PERCENTAGE},
            borders:noB(),
          }),
          // PASS/FAIL badge
          new TableCell({
            children:[new Paragraph({children:[new TextRun({text:status,bold:true,size:17,color:WHITE_,font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:60,after:60}})],
            shading:{type:ShadingType.CLEAR,fill:sc},
            margins:{top:100,bottom:100,left:80,right:80},
            width:{size:10,type:WidthType.PERCENTAGE},
            borders:{...noB()},
          }),
          // Assessment
          new TableCell({
            children:[new Paragraph({children:[new TextRun({text:asmt,size:17,color:sc,font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:60,after:60}})],
            shading:{type:ShadingType.CLEAR,fill:scLight},
            margins:{top:100,bottom:100,left:80,right:80},
            width:{size:14,type:WidthType.PERCENTAGE},
            borders:{...noB()},
          }),
        ]});
      });

      const hdr = new TableRow({
        children:['Skill Domain','Performance','Score','Status','Assessment'].map((h,i)=>
          new TableCell({
            children:[new Paragraph({children:[new TextRun({text:h,bold:true,size:17,color:WHITE_,font:'Calibri'})],alignment:i===0?AlignmentType.LEFT:AlignmentType.CENTER})],
            shading:{type:ShadingType.CLEAR,fill:NAVY},
            margins:{top:100,bottom:100,left:160,right:100},
            borders:noB(),
          })
        ),
        tableHeader:true,
      });

      return new Table({rows:[hdr,...rows],width:{size:100,type:WidthType.PERCENTAGE}});
    }

    const doc=new Document({
      creator:'NexaCyberSim',
      title:`Simulation Report — ${clientName||'Client'}`,
      styles:{default:{document:{run:{font:'Calibri',size:20}}}},
      sections:[{
        properties:{page:{margin:{top:680,bottom:680,left:960,right:960}}},
        headers:{default:new Header({children:[
          new Table({
            width:{size:100,type:WidthType.PERCENTAGE},
            borders:{...noB(),insideH:{style:BorderStyle.NONE},insideV:{style:BorderStyle.NONE}},
            rows:[new TableRow({children:[
              new TableCell({children:[new Paragraph({children:[
                new TextRun({text:'NEXACYBERSIM',bold:true,size:16,color:NAVY,font:'Calibri'}),
                new TextRun({text:'  |  Executive Simulation Report',size:15,color:LIGHT,font:'Calibri'}),
              ]})],borders:noB(),margins:{top:60,bottom:60}}),
              new TableCell({children:[new Paragraph({children:[
                new TextRun({text:'CONFIDENTIAL',bold:true,size:15,color:G_RED,font:'Calibri',characterSpacing:40}),
              ],alignment:AlignmentType.RIGHT})],borders:noB(),margins:{top:60,bottom:60}}),
            ]})],
          }),
          new Paragraph({border:{bottom:{color:ACCENT,size:6,style:BorderStyle.SINGLE}},spacing:{before:0,after:0}}),
        ]})},
        footers:{default:new Footer({children:[
          new Paragraph({border:{top:{color:SILVER,size:4,style:BorderStyle.SINGLE}},spacing:{before:0,after:60}}),
          new Paragraph({children:[
            new TextRun({text:`${clientName||'Client'}`,size:15,color:MID,font:'Calibri'}),
            new TextRun({text:`  ·  ${scenarioTitle}  ·  ${date}  ·  `,size:15,color:LIGHT,font:'Calibri'}),
            new TextRun({text:'Confidential',size:15,color:LIGHT,italics:true,font:'Calibri'}),
          ],alignment:AlignmentType.CENTER}),
        ]})},
        children:[
          // ── COVER PAGE ──

          // Navy banner — full DXA width for reliable Word rendering
          new Table({
            width:{size:9638,type:WidthType.DXA},
            columnWidths:[9638],
            borders:{...noB(),insideH:{style:BorderStyle.NONE},insideV:{style:BorderStyle.NONE}},
            rows:[new TableRow({children:[
              new TableCell({
                children:[
                  new Paragraph({children:[new TextRun({text:' ',size:8})],spacing:{before:320,after:0}}),
                  new Paragraph({children:[new TextRun({text:'NEXACYBERSIM',bold:true,size:72,color:WHITE_,font:'Calibri',characterSpacing:20})],alignment:AlignmentType.CENTER,spacing:{before:0,after:0}}),
                  new Paragraph({children:[new TextRun({text:'Enterprise Cyber Crisis Simulation',size:26,color:'A8C4E0',font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:80,after:80}}),
                  new Paragraph({children:[new TextRun({text:'EXECUTIVE PERFORMANCE REPORT',bold:true,size:20,color:'7BA7CC',font:'Calibri',characterSpacing:80})],alignment:AlignmentType.CENTER,spacing:{after:0}}),
                  new Paragraph({children:[new TextRun({text:' ',size:8})],spacing:{after:320}}),
                ],
                shading:{type:ShadingType.CLEAR,fill:NAVY},
                borders:noB(),
              }),
            ]})],
          }),

          // Spacer — separates banner from grade block
          new Paragraph({children:[new TextRun({text:' ',size:4})],spacing:{before:0,after:0}}),

          // Grade block — centered, standalone
          new Paragraph({children:[new TextRun({text:`Grade ${grade}`,bold:true,size:80,color:gradeColor,font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:240,after:0}}),
          new Paragraph({children:[new TextRun({text:`${pct}%  —  ${pct>=90?'Excellent':pct>=70?'Competent':pct>=50?'Developing':'Critical Risk'}`,bold:true,size:28,color:gradeColor,font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:0,after:0}}),
          new Paragraph({children:[new TextRun({text:`${correctCount} of ${totalDecisions} decisions correct`,size:22,color:MID,font:'Calibri'})],alignment:AlignmentType.CENTER,spacing:{before:60,after:0}}),

          // Spacer — separates grade from info table
          new Paragraph({children:[new TextRun({text:' ',size:4})],spacing:{before:0,after:200}}),

          // Info table — fixed DXA width, centered
          new Table({
            width:{size:6000,type:WidthType.DXA},
            columnWidths:[2000,4000],
            alignment:AlignmentType.CENTER,
            borders:{...noB(),insideH:{style:BorderStyle.NONE},insideV:{style:BorderStyle.NONE}},
            rows:[
              infoRow('Client Organisation',clientName||'Confidential',true),
              infoRow('Scenario',scenarioTitle||'',false),
              infoRow('Participant Level',level?level.charAt(0).toUpperCase()+level.slice(1)+' Level':'',true),
              infoRow('Report Date',date||'',false),
              infoRow('Overall Grade',`${grade} — ${pct}%`,true),
            ],
          }),

          // Spacer before page break
          new Paragraph({children:[new TextRun({text:' ',size:4})],spacing:{before:0,after:0}}),
          new Paragraph({children:[new PageBreak()]}),

          // ── SECTION 1: Performance Summary ──
          secHead('1. Performance Summary'),
          new Paragraph({spacing:{after:180}}),
          metricTable([
            {val:`${score}/${maxScore}`,lbl:'Total Score'},
            {val:`${pct}%`,lbl:'Performance'},
            {val:`${correctCount}/${totalDecisions}`,lbl:'Correct Decisions'},
            {val:`Grade ${grade}`,lbl:'Final Grade'},
          ]),
          new Paragraph({spacing:{after:220}}),
          new Paragraph({
            children:[
              new TextRun({text:'Overall Grade  ',bold:true,size:24,color:DARK,font:'Calibri'}),
              new TextRun({text:grade,bold:true,size:40,color:gradeColor,font:'Calibri'}),
              new TextRun({text:`  —  ${pct>=90?'Excellent':pct>=70?'Competent':pct>=50?'Developing':'Critical Risk'}`,size:26,color:gradeColor,font:'Calibri'}),
            ],
            spacing:{after:100},
            shading:{type:ShadingType.CLEAR,fill:gradeColor==='1B6B3A'?'E8F5EE':gradeColor==='1E40AF'?'EEF4FB':gradeColor==='92400E'?'FEF3C7':'FEE2E2'},
            indent:{left:160},
            border:{left:{color:gradeColor,size:24,style:BorderStyle.SINGLE}},
          }),
          bPara(pct>=90?'Outstanding incident response capability across all tested domains.':pct>=70?'Solid capability with identifiable areas for targeted improvement.':pct>=50?'Partial capability. Significant gaps would impact real-world response effectiveness.':'Participant unable to effectively navigate the scenario. Immediate remediation required.',{color:MID}),
          hRule(),

          // ── SECTION 2: Skill Domain Performance ──
          secHead('2. Skill Domain Performance'),
          new Paragraph({spacing:{after:160}}),
          // Radar chart image (centered)
          ...(radarPNG ? [new Paragraph({
            children:[new ImageRun({
              data: radarPNG,
              transformation:{ width:320, height:320 },
              type:'png',
            })],
            alignment:AlignmentType.CENTER,
            spacing:{after:120},
          })] : []),

          // ── Radar Legend ──
          new Paragraph({
            children:[
              new TextRun({text:'Legend:  ',bold:true,size:18,color:MID,font:'Calibri'}),
              new TextRun({text:'● ',bold:true,size:22,color:G_GREEN,font:'Calibri'}),
              new TextRun({text:'PASS  ≥70%',size:18,color:G_GREEN,font:'Calibri'}),
              new TextRun({text:'     ● ',bold:true,size:22,color:G_AMBER,font:'Calibri'}),
              new TextRun({text:'DEVELOPING  50–69%',size:18,color:G_AMBER,font:'Calibri'}),
              new TextRun({text:'     ● ',bold:true,size:22,color:G_RED,font:'Calibri'}),
              new TextRun({text:'FAIL  <50%',size:18,color:G_RED,font:'Calibri'}),
            ],
            alignment:AlignmentType.CENTER,
            spacing:{before:0,after:200},
          }),
          skillBarTable(skills),
          new Paragraph({spacing:{after:120}}),
          new Paragraph({
            children:[new TextRun({text:passNote,size:18,color:MID,italics:true,font:'Calibri'})],
            spacing:{after:80},
            indent:{left:160},
          }),
          hRule(),

          // ── SECTION 3: Consultant's Executive Analysis ──
          secHead("3. Consultant's Executive Analysis"),
          new Paragraph({spacing:{after:140}}),
          ...conclusionParas,
          hRule(),

          // ── SECTION 4: Decision-by-Decision Analysis ──
          secHead('4. Decision-by-Decision Analysis'),
          new Paragraph({spacing:{after:160}}),
          decisionsTable(decisions),
          hRule(),

          // ── SECTION 5: Regulatory & Framework Alignment ──
          secHead('5. Regulatory & Framework Alignment'),
          new Paragraph({spacing:{after:120}}),
          bPara('This simulation assessed responses against the following internationally recognised frameworks:',{color:MID}),
          new Paragraph({spacing:{after:80}}),
          ...(frameworks||[]).map(f=>bBullet(f,ACCENT)),
          new Paragraph({spacing:{after:280}}),

          // Disclaimer
          new Paragraph({
            children:[new TextRun({text:'DISCLAIMER',bold:true,size:15,color:LIGHT,font:'Calibri',characterSpacing:60})],
            spacing:{before:200,after:60},
            border:{top:{color:SILVER,size:4,style:BorderStyle.SINGLE}},
          }),
          new Paragraph({
            children:[new TextRun({text:'This report is generated from a tabletop crisis simulation and is for internal training purposes only. It should not be interpreted as a security audit or penetration test. Confidential — intended solely for the recipient organisation.',size:16,color:LIGHT,italics:true,font:'Calibri'})],
            spacing:{after:80},
          }),
          new Paragraph({
            children:[new TextRun({text:`Generated by NexaCyberSim  •  ${date}  •  Confidential`,size:15,color:LIGHT,italics:true,font:'Calibri'})],
            alignment:AlignmentType.CENTER,
          }),
        ],
      }],
    });

    let buffer = await Packer.toBuffer(doc);

    // ── POST-PROCESS: Fix shading XML — docx library puts color in w:color but Word needs w:fill ──
    // Unzip, patch XML, rezip
    const JSZip = (() => {
      try { return require('jszip'); } catch(e) { return null; }
    })();
    if(JSZip){
      try {
        const zip = await JSZip.loadAsync(buffer);
        const docXml = zip.file('word/document.xml');
        if(docXml){
          let xml = await docXml.async('string');
          // Fix: <w:shd w:color="XXXXXX" w:val="solid"/> → <w:shd w:fill="XXXXXX" w:color="auto" w:val="clear"/>
          xml = xml.replace(/<w:shd w:color="([0-9A-Fa-f]{6})" w:val="solid"\/>/g,
            '<w:shd w:fill="$1" w:color="auto" w:val="clear"/>');
          // Also fix table cell shading
          xml = xml.replace(/<w:shd w:color="([0-9A-Fa-f]{6})" w:val="solid"\/>/g,
            '<w:shd w:fill="$1" w:color="auto" w:val="clear"/>');
          zip.file('word/document.xml', xml);
          buffer = await zip.generateAsync({type:'nodebuffer', compression:'DEFLATE'});
        }
      } catch(zipErr) {
        console.warn('Post-process shading fix failed (non-fatal):', zipErr.message);
      }
    }

    const filename=`NexaCyberSim_${(clientName||'Report').replace(/\s+/g,'_')}_${new Date().toISOString().split('T')[0]}.docx`;
    res.setHeader('Content-Disposition',`attachment; filename="${filename}"`);
    res.setHeader('Content-Type','application/vnd.openxmlformats-officedocument.wordprocessingml.document');
    res.send(buffer);

  } catch(err){
    console.error('Word export error:',err.message);
    res.status(500).json({error:'Failed to generate Word document'});
  }
});

// ─────────────────────────────────────────────
// FREE-TEXT RESPONSE GRADING — protected + rate limited
// ─────────────────────────────────────────────
app.post('/api/grade-response', requireAuth, aiLimiter, async (req, res) => {
  try {
    const answer = sanitiseString(req.body.answer || '', 3000);
    const question = sanitiseString(req.body.question || '', 1000);
    const expectedActions = sanitiseString(req.body.expectedActions || req.body.correctFeedback || '', 3000);
    if (!answer) return res.status(400).json({ error: 'answer is required' });

    const completion = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      temperature: 0.2,
      max_tokens: 800,
      response_format: { type: 'json_object' },
      messages: [
        { role: 'system', content: `You are a strict but fair cybersecurity tabletop exercise evaluator.
Evaluate the participant free-text response against the expected/playbook-aligned actions.
Return ONLY valid JSON with this exact shape:
{
  "score": 0-100,
  "branch": "strong" | "partial" | "weak",
  "matchedActions": ["..."],
  "missingActions": ["..."],
  "riskyActions": ["..."],
  "feedback": "short professional feedback"
}
Scoring: 80-100 strong, 50-79 partial, 0-49 weak.` },
        { role: 'user', content: `Question:
${question}

Expected actions:
${expectedActions}

Participant response:
${answer}` }
      ]
    });

    const parsed = JSON.parse(completion.choices[0]?.message?.content || '{}');
    const score = Math.max(0, Math.min(100, Number(parsed.score || 0)));
    const branch = parsed.branch || (score >= 80 ? 'strong' : score >= 50 ? 'partial' : 'weak');
    res.json({
      score,
      branch,
      matchedActions: Array.isArray(parsed.matchedActions) ? parsed.matchedActions : [],
      missingActions: Array.isArray(parsed.missingActions) ? parsed.missingActions : [],
      riskyActions: Array.isArray(parsed.riskyActions) ? parsed.riskyActions : [],
      feedback: parsed.feedback || ''
    });
  } catch (err) {
    console.error('Grade response error:', err.message);
    res.status(500).json({ error: 'Failed to grade response' });
  }
});

// ─────────────────────────────────────────────
// CATCH-ALL — serve HTML app
// ─────────────────────────────────────────────
app.get('/{*path}', (req, res) => {
  const indexFile = path.join(PUBLIC_DIR, 'index.html');
  if (fs.existsSync(indexFile)) {
    res.sendFile(indexFile);
  } else {
    res.status(404).send('Application not found. Make sure public/index.html exists.');
  }
});

// ─────────────────────────────────────────────
// A05 — GLOBAL ERROR HANDLER (no stack trace leaks)
// ─────────────────────────────────────────────
app.use((err, req, res, next) => {
  console.error('Unhandled error:', err.message);
  res.status(500).json({ error: 'Internal server error' });
});

const PORT = process.env.PORT || 8080;
app.listen(PORT, '0.0.0.0', () => {
  console.log(`NexaCyberSim running on port ${PORT}`);
  console.log(`Environment: ${process.env.NODE_ENV || 'development'}`);
});
