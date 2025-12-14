// background.js - service worker
const TRACK_KEY = 'tracked_items';
const CONSENT_KEY = 'share_consent';

// store item structure: { id, url, title, priceHistory: [{price,ts}], site }

chrome.runtime.onInstalled.addListener(()=> {
  console.log('Tiny Price Tracker installed');
});

chrome.runtime.onMessage.addListener((msg, sender) => {
  if (msg.type === 'PRODUCT_INFO') {
    // content script found a product and sent info
    const info = msg.payload;
    // try to find matching tracked item by url
    chrome.storage.local.get([TRACK_KEY, CONSENT_KEY], data => {
      const tracked = data[TRACK_KEY] || {};
      const consent = data[CONSENT_KEY] || false;
      const key = info.url; // simple key, could be product id
      if (tracked[key]) {
        // append price point
        tracked[key].priceHistory = tracked[key].priceHistory || [];
        tracked[key].priceHistory.push({price: info.price, priceText: info.priceText, ts: info.timestamp});
      } else {
        // not tracked yet; notify popup that product exists for quick add
        // Save a 'lastSeen' entry to show in popup
        chrome.storage.local.set({ lastSeen: info });
      }
      chrome.storage.local.set({ [TRACK_KEY]: tracked });
      // If consented, send anonymized event (non-PII)
      if (consent) {
        sendAnonymizedEvent({site: info.site, price: info.price, ts: info.timestamp});
      }
    });
  } else if (msg.type === 'TRACK_URL') {
    const info = msg.payload;
    chrome.storage.local.get(TRACK_KEY, data => {
      const tracked = data[TRACK_KEY] || {};
      const key = info.url;
      tracked[key] = tracked[key] || { id: key, url: key, title: info.title, site: info.site, priceHistory: [] };
      if (info.price) tracked[key].priceHistory.push({price: info.price, priceText: info.priceText, ts: info.timestamp});
      chrome.storage.local.set({ [TRACK_KEY]: tracked }, ()=> {
        chrome.runtime.sendMessage({type:'TRACKED_UPDATED'});
      });
    });
  }
});

function sendAnonymizedEvent(event) {
  try {
    // example: calls your serverless endpoint; only run if you've configured it in options
    chrome.storage.local.get('server_endpoint', data => {
      const ep = data.server_endpoint;
      if (!ep) return;
      // prepare anonymized payload
      const payload = {
        site: event.site,
        price: event.price,
        ts: event.ts,
        // do not include url or title to avoid PII on default
      };
      fetch(ep, {
        method: 'POST',
        headers: {'Content-Type':'application/json'},
        body: JSON.stringify(payload)
      }).catch(e => console.warn('sendAnonymizedEvent failed', e));
    });
  } catch (e) {
    console.warn(e);
  }
}
